/-
# Explicit continuity of the ORIGINAL thermodynamic OS pairing

Sharp Cauchy--Schwarz and the semantic bilinear difference identity give
the same square-root-free tolerance epsilon^2/(8*(B+1)) for the constructed
common-volume pairing. Only generic rational tolerance estimates are reused
from the finite pairing module; every form and squared distance below is
the ORIGINAL thermodynamic one. No boundedness premise is silently supplied.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
import YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity
  (smallTolerance smallTolerance_pos smallTolerance_budget signed_small_of_square
    pairingTolerance pairingTolerance_pos)

private theorem rc_telescope (a b c : RC) : RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    (Q'.add_eqv_congr_right _ _ _ (Q'.sub_add_cancel_eqv _ _))

theorem presentedForm_symm (p q : Presentation) :
    Equiv (presentedForm p q) (presentedForm q p) :=
  Quotient.exact (pairing_symm (embed p) (embed q))

theorem presentedForm_nonnegative (p : Presentation) : leEv czero (presentedForm p p) :=
  pairing_nonnegative (embed p)

theorem presentedForm_cauchySchwarz (p q : Presentation) :
    leEv (CReal.mul (presentedForm p q) (presentedForm p q))
      (CReal.mul (presentedForm p p) (presentedForm q q)) :=
  pairing_cauchySchwarz (embed p) (embed q)

theorem pairing_small (p q : Presentation) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (hp : leEv (presentedForm p p) (ofQ' (smallTolerance B hB r)))
    (hq : leEv (presentedForm q q) (ofQ' B)) :
    leRat (presentedForm p q) r ∧ leRat (CReal.neg (presentedForm p q)) r := by
  apply signed_small_of_square _ r hr
  have hcs := pairing_cauchySchwarz (embed p) (embed q)
  let deltaR : RC := Quotient.mk crealSetoid (ofQ' (smallTolerance B hB r))
  let boundR : RC := Quotient.mk crealSetoid (ofQ' B)
  have hpR : RCle (pairing (embed p) (embed p)) deltaR := hp
  have hqR : RCle (pairing (embed q) (embed q)) boundR := hq
  have hdeltaR : RCnonneg deltaR :=
    CReal.leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := RCle_trans hcs (RCle_trans
    (mul_mono_right (pairing_nonnegative (embed q)) hpR)
    (mul_mono_left hdeltaR hqR))
  exact leEv_trans hprod (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr))

theorem form_difference_split (p p' q q' : Presentation) :
    Equiv (CReal.sub (presentedForm p q) (presentedForm p' q'))
      (CReal.add (presentedForm (presentationSubtract p p') q)
        (presentedForm (presentationSubtract q q') p')) := by
  apply Quotient.exact (s := crealSetoid)
  change RCsub (pairing (embed p) (embed q)) (pairing (embed p') (embed q')) =
    RCadd (pairing (subtract (embed p) (embed p')) (embed q))
      (pairing (subtract (embed q) (embed q')) (embed p'))
  rw [pairing_sub_left, pairing_symm (subtract (embed q) (embed q')) (embed p'), pairing_sub_right]
  exact (rc_telescope _ _ _).symm

/-- Only the two unchanged vectors require norm bounds, on the SAME form. -/
theorem pairing_close (e e' f f' : Presentation) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (he : leEv (distSq e e') (ofQ' (pairingTolerance B hB epsilon)))
    (hf : leEv (distSq f f') (ofQ' (pairingTolerance B hB epsilon)))
    (hfnorm : leEv (presentedForm f f) (ofQ' B))
    (henorm : leEv (presentedForm e' e') (ofQ' B)) :
    leRat (CReal.sub (presentedForm e f) (presentedForm e' f')) epsilon ∧
    leRat (CReal.sub (presentedForm e' f') (presentedForm e f)) epsilon := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small (presentationSubtract e e') f B hB _ hr he hfnorm
  have h2 := pairing_small (presentationSubtract f f') e' B hB _ hr hf henorm
  have hsplit := form_difference_split e e' f f'
  have hreverse : Equiv (CReal.sub (presentedForm e' f') (presentedForm e f))
      (CReal.add (CReal.neg (presentedForm (presentationSubtract e e') f))
        (CReal.neg (presentedForm (presentationSubtract f f') e'))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.presentedForm_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.presentedForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.presentedForm_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.form_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPairingContinuity.pairing_close
