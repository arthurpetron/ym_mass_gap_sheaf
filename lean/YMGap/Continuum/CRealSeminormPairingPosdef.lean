/-
# Constructive separation of a completed squared-seminorm pairing

The supplied dense distance-to-zero identity ties the existing distance
to the actual pairing diagonal. A zero representative limit then yields
Type-valued closeness to the constant zero stream, with modulus exactly
the computed pairing rate. No representative or convergence modulus is
selected from a propositional existence statement.

Positive definiteness is proved on the SAME D.Completion quotient. Sharp
Cauchy--Schwarz also passes from the supplied dense law through the same
pairing limits. These results assume neither completed linearity nor
metric completeness and introduce no physical frontier fields.
-/

import YMGap.Continuum.CRealSeminormPairingCompletion
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.CRealSeminormPairingCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPosdef (late_limit_bound)

variable {D : SquaredSeminorm} (P : PairingData D)

/-- The actual outer rate controls every late term against its scalar limit. -/
theorem pairSequence_limit_close (X Y : D.Cauchy)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : pairRate P X Y epsilon ≤ n) :
    leRat (sub (pairSequence P X Y n) (representativeInner P X Y)) epsilon ∧
    leRat (sub (representativeInner P X Y) (pairSequence P X Y n)) epsilon :=
  late_limit_bound (pairSequence_converges P X Y)
    (pairSequence_bound P X Y) epsilon he n hn

/-- The closeness witness retains the existing computable pairing rate. -/
def closeZeroOfInnerZero (z : D.Carrier)
    (hdist : ∀ x, Equiv (D.distSq x z) (P.pairing x x)) (X : D.Cauchy)
    (h : Equiv (representativeInner P X X) czero) :
    D.Close X (D.constant z) where
  modulus := pairRate P X X
  close := by
    intro epsilon he n hn
    have hbound := (pairSequence_limit_close P X X epsilon he n hn).1
    have hsub : Equiv
        (sub (pairSequence P X X n) (representativeInner P X X))
        (pairSequence P X X n) :=
      (CReal.sub_congr_right h).trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (Q'.eqv_of_eq (Q'.add_zero' ((pairSequence P X X n).approx k)))))
    exact leEv_trans (leEv_of_equiv (hdist (X.seq n)))
      (CReal.leRat_of_equiv hsub.symm hbound)

theorem closeZeroOfInnerZero_modulus (z : D.Carrier)
    (hdist : ∀ x, Equiv (D.distSq x z) (P.pairing x x)) (X : D.Cauchy)
    (h : Equiv (representativeInner P X X) czero) :
    (closeZeroOfInnerZero P z hdist X h).modulus = pairRate P X X := rfl

theorem completedZero_inner_zero (z : D.Carrier)
    (hz : Equiv (P.pairing z z) czero) :
    completedInner P (D.embedRep z) (D.embedRep z) = RCzero := by
  rw [completedInner_embedRep]
  exact Quotient.sound hz

/-- Zero completed norm is exactly equality with the embedded dense zero. -/
theorem completedInner_posdef (z : D.Carrier)
    (hdist : ∀ x, Equiv (D.distSq x z) (P.pairing x x))
    (hz : Equiv (P.pairing z z) czero) (x : D.Completion) :
    completedInner P x x = RCzero ↔ x = D.embedRep z := by
  constructor
  · refine Quotient.inductionOn x ?_
    intro X h
    exact Quotient.sound ⟨closeZeroOfInnerZero P z hdist X (Quotient.exact h)⟩
  · intro h
    rw [h]
    exact completedZero_inner_zero P z hz

/-- Sharp dense CS passes through actual mixed and diagonal scalar limits. -/
theorem representativeInner_cauchySchwarz
    (hCS : ∀ x y, leEv (mul (P.pairing x y) (P.pairing x y))
      (mul (P.pairing x x) (P.pairing y y))) (X Y : D.Cauchy) :
    leEv (mul (representativeInner P X Y) (representativeInner P X Y))
      (mul (representativeInner P X X) (representativeInner P Y Y)) :=
  leEv_of_convergesTo_le
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges P X Y) (pairSequence_converges P X Y))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (pairSequence_converges P X X) (pairSequence_converges P Y Y))
    (fun n => hCS (X.seq n) (Y.seq n))

theorem completedInner_cauchySchwarz
    (hCS : ∀ x y, leEv (mul (P.pairing x y) (P.pairing x y))
      (mul (P.pairing x x) (P.pairing y y))) (x y : D.Completion) :
    RCle (RCmul (completedInner P x y) (completedInner P x y))
      (RCmul (completedInner P x x) (completedInner P y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact representativeInner_cauchySchwarz P hCS

/-- A nonnegative scalar dominated by a strict contraction of itself is
zero. The cancelled factor is the positive margin 1-rate, not the scalar. -/
theorem scalar_contraction_zero (rate : Q') (hrate : rate < (1 : Q'))
    (a : RC) (hnon : RCnonneg a)
    (hcontract : RCle a (RCmul (Quotient.mk crealSetoid (ofQ' rate)) a)) : a = RCzero := by
  revert hnon hcontract
  refine Quotient.inductionOn a ?_
  intro A hnon hcontract
  have hmargin : (0 : Q') < 1 + -rate := HKPos.one_sub_pos hrate
  have hproduct : leEv (mul A (ofQ' (1 + -rate))) (mul czero (ofQ' (1 + -rate))) := by
    intro epsilon he
    obtain ⟨N, hN⟩ := hcontract epsilon he
    refine ⟨N, fun n hn => ?_⟩
    have hsub := Q'.sub_le_of_le_add (hN n hn)
    have heq : Q'.eqv (A.approx n * (1 + -rate)) (A.approx n + -(rate * A.approx n)) :=
      RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
        (.add (.var 0) (.neg (.mul (.var 1) (.var 0))))
        (by decide) (fun i => if i = 0 then A.approx n else rate)
    have hz : Q'.eqv ((0 : Q') * (1 + -rate) + epsilon) epsilon :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _))
        (Q'.eqv_of_eq (Q'.zero_add' epsilon))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
      (Q'.le_trans' _ _ _ hsub (Q'.ge_of_eqv hz))
  have hzero : leEv A czero :=
    RCBilinearDifference.cancel_positive_factor (1 + -rate) hmargin
      (fun _ => Q'.le_refl' _) hproduct
  exact Quotient.sound (equiv_of_leEv_leEv hzero hnon)

end YMGap.Continuum.CRealSeminormPairingCompletion

#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.pairSequence_limit_close
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.closeZeroOfInnerZero
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.closeZeroOfInnerZero_modulus
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedZero_inner_zero
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_posdef
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.representativeInner_cauchySchwarz
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.completedInner_cauchySchwarz
#print axioms YMGap.Continuum.CRealSeminormPairingCompletion.scalar_contraction_zero
