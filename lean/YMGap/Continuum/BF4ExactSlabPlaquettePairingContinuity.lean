/-
# Explicit continuity of the ORIGINAL normalized reflected plaquette pairing

The input tolerance is epsilon^2/(8*(B+1)), where B bounds the two
unchanged diagonal forms. Sharp CS, a spare half-square budget and the
two-term bilinear difference identity give two-sided pairing error epsilon.
The bound and tolerance are data; no square root or choice is required.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
import YMGap.Continuum.ScaledGNSCompletionEstimates

namespace YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates

private theorem plus_one_pos {B : Q'} (hB : (0 : Q') ≤ B) : (0 : Q') < B + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 B hB) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def smallTolerance (B : Q') (hB : (0 : Q') ≤ B) (r : Q') : Q' :=
  Q'.divPos (HalfPow.half * (r * r)) (B + 1) (plus_one_pos hB)

theorem smallTolerance_pos (B : Q') (hB : (0 : Q') ≤ B) {r : Q'} (hr : (0 : Q') < r) :
    (0 : Q') < smallTolerance B hB r :=
  Q'.divPos_pos _ _ _ (ExpNeg.half_mul_pos _ (Q'.mul_pos hr hr))

theorem smallTolerance_budget (B : Q') (hB : (0 : Q') ≤ B) {r : Q'} (hr : (0 : Q') < r) :
    smallTolerance B hB r * B ≤ HalfPow.half * (r * r) :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg B 1 Q'.zero_le_one)
      (Q'.le_of_lt (smallTolerance_pos B hB hr)))
    (Q'.le_of_eqv (Q'.divPos_mul_eqv _ _ _))

/-- A spare half-square turns eventual CS into an eventual absolute bound. -/
theorem signed_small_of_square (A : CReal) (r : Q') (hr : (0 : Q') < r)
    (h : leEv (CReal.mul A A) (ofQ' (HalfPow.half * (r * r)))) :
    leRat A r ∧ leRat (CReal.neg A) r := by
  obtain ⟨N, hN⟩ := h (HalfPow.half * (r * r)) (ExpNeg.half_mul_pos _ (Q'.mul_pos hr hr))
  have hb : ∀ n, N ≤ n → A.approx n ≤ r ∧ -A.approx n ≤ r := by
    intro n hn
    exact Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq hr
      (Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (ExpNeg.two_halves (r * r)))))
  exact ⟨leRat_of_eventually ⟨N, fun n hn => (hb n hn).1⟩,
    leRat_of_eventually ⟨N, fun n hn => (hb n hn).2⟩⟩

private theorem rc_telescope (a b c : RC) : RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    (Q'.add_eqv_congr_right _ _ _ (Q'.sub_add_cancel_eqv _ _))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

theorem pairing_small (e f : PlaquetteExpression half) (B : Q') (hB : (0 : Q') ≤ B)
    (r : Q') (hr : (0 : Q') < r)
    (he : leEv (form w hw0 hw1 e e) (ofQ' (smallTolerance B hB r)))
    (hf : leEv (form w hw0 hw1 f f) (ofQ' B)) :
    leRat (form w hw0 hw1 e f) r ∧ leRat (CReal.neg (form w hw0 hw1 e f)) r := by
  apply signed_small_of_square _ r hr
  have hcs : RCle (RCmul (pairing w hw0 hw1 e f) (pairing w hw0 hw1 e f))
      (RCmul (pairing w hw0 hw1 e e) (pairing w hw0 hw1 f f)) := form_cauchySchwarz w hw0 hw1 e f
  let deltaR : RC := Quotient.mk crealSetoid (ofQ' (smallTolerance B hB r))
  let boundR : RC := Quotient.mk crealSetoid (ofQ' B)
  have heR : RCle (pairing w hw0 hw1 e e) deltaR := he
  have hfR : RCle (pairing w hw0 hw1 f f) boundR := hf
  have hdeltaR : RCnonneg deltaR :=
    CReal.leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (smallTolerance_pos B hB hr))
  have hprod := RCle_trans hcs (RCle_trans
    (mul_mono_right (pairing_nonnegative w hw0 hw1 f) heR)
    (mul_mono_left hdeltaR hfR))
  exact leEv_trans hprod (leEv_le_ofQ'_of_approx_le (fun _ => smallTolerance_budget B hB hr))

theorem form_difference_split (e e' f f' : PlaquetteExpression half) :
    Equiv (CReal.sub (form w hw0 hw1 e f) (form w hw0 hw1 e' f'))
      (CReal.add (form w hw0 hw1 (subtract e e') f) (form w hw0 hw1 (subtract f f') e')) := by
  apply Quotient.exact (s := crealSetoid)
  change RCsub (pairing w hw0 hw1 e f) (pairing w hw0 hw1 e' f') =
    RCadd (pairing w hw0 hw1 (subtract e e') f) (pairing w hw0 hw1 (subtract f f') e')
  rw [pairing_sub_left, pairing_symm w hw0 hw1 (subtract f f') e', pairing_sub_right]
  exact (rc_telescope _ _ _).symm

def pairingTolerance (B : Q') (hB : (0 : Q') ≤ B) (epsilon : Q') : Q' :=
  smallTolerance B hB (HalfPow.half * epsilon)

theorem pairingTolerance_pos (B : Q') (hB : (0 : Q') ≤ B) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < pairingTolerance B hB epsilon := smallTolerance_pos B hB (ExpNeg.half_mul_pos epsilon he)

/-- Only the two unchanged vectors require norm bounds, on the SAME form. -/
theorem pairing_close (e e' f f' : PlaquetteExpression half) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (he : leEv (distSq w hw0 hw1 e e') (ofQ' (pairingTolerance B hB epsilon)))
    (hf : leEv (distSq w hw0 hw1 f f') (ofQ' (pairingTolerance B hB epsilon)))
    (hfnorm : leEv (form w hw0 hw1 f f) (ofQ' B))
    (henorm : leEv (form w hw0 hw1 e' e') (ofQ' B)) :
    leRat (CReal.sub (form w hw0 hw1 e f) (form w hw0 hw1 e' f')) epsilon ∧
    leRat (CReal.sub (form w hw0 hw1 e' f') (form w hw0 hw1 e f)) epsilon := by
  have hr := ExpNeg.half_mul_pos epsilon hepsilon
  have h1 := pairing_small w hw0 hw1 (subtract e e') f B hB _ hr he hfnorm
  have h2 := pairing_small w hw0 hw1 (subtract f f') e' B hB _ hr hf henorm
  have hsplit := form_difference_split w hw0 hw1 e e' f f'
  have hreverse : Equiv (CReal.sub (form w hw0 hw1 e' f') (form w hw0 hw1 e f))
      (CReal.add (CReal.neg (form w hw0 hw1 (subtract e e') f))
        (CReal.neg (form w hw0 hw1 (subtract f f') e'))) :=
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.neg_sub_eqv _ _))).trans
      ((CReal.neg_congr hsplit).trans (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _)))
  exact ⟨CReal.leRat_of_equiv hsplit
      (leRat_mono (leRat_add h1.1 h2.1) (Q'.le_of_eqv (ExpNeg.two_halves epsilon))),
    CReal.leRat_of_equiv hreverse
      (leRat_mono (leRat_add h1.2 h2.2) (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))⟩

end YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity

#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.smallTolerance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.smallTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.smallTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.signed_small_of_square
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.pairing_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.form_difference_split
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.pairingTolerance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.pairingTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity.pairing_close
