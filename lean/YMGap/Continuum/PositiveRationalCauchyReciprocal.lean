/-
# Reciprocal of a rational Cauchy stream with a witnessed positive floor

The reciprocal stream has the explicit modulus M(epsilon / (1/b)^2).
Its completed product with the ORIGINAL stream limit is one. All data are
computed from the supplied stream, modulus and rational floor; no positive
real reciprocal or modulus is selected from a propositional existence claim.
-/

import YMGap.Continuum.SummableRationalReciprocalStepVariation
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.ArtanhMonotone
import YMGap.Constructive.TrigAddCReal
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.PositiveRationalCauchyReciprocal

set_option autoImplicit false

open YMGap.Constructive

variable {r : Nat → Q'} (c : CReal.QCauchy r) (b : Q') (hb : (0 : Q') < b)
    (hfloor : ∀ n, b ≤ r n)

def term (n : Nat) : Q' :=
  Q'.recipPos (r n) (Q'.pos_of_lt_of_le hb (hfloor n))

theorem term_pos (n : Nat) : (0 : Q') < term b hb hfloor n :=
  Q'.recipPos_pos _ _

theorem term_le (n : Nat) : term b hb hfloor n ≤ Q'.recipPos b hb :=
  ArtanhMonotone.recipPos_antitone _ _ hb _ (hfloor n)

def sensitivity : Q' := Q'.recipPos b hb * Q'.recipPos b hb

theorem sensitivity_pos : (0 : Q') < sensitivity b hb :=
  Q'.mul_pos (Q'.recipPos_pos b hb) (Q'.recipPos_pos b hb)

def tolerance (epsilon : Q') : Q' :=
  Q'.divPos epsilon (sensitivity b hb) (sensitivity_pos b hb)

theorem tolerance_pos {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance b hb epsilon :=
  Q'.divPos_pos _ _ _ he

theorem tolerance_budget (epsilon : Q') :
    Q'.eqv (sensitivity b hb * tolerance b hb epsilon) epsilon :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv _ _ _)

/-- Explicit reciprocal modulus, without a new convergence premise. -/
def reciprocalCauchy : CReal.QCauchy (term b hb hfloor) where
  M epsilon := c.M (tolerance b hb epsilon)
  bound := by
    intro epsilon he p q hp hq
    have hd := tolerance_pos b hb he
    have hh := c.bound (tolerance b hb epsilon) hd p q hp hq
    have step (i j : Nat) (h : r j ≤ r i + tolerance b hb epsilon) :
        term b hb hfloor i ≤ term b hb hfloor j + epsilon :=
      Q'.le_trans' _ _ _
        (SummableRationalReciprocalStepVariation.reciprocal_step_le
          (r i) (r j) (tolerance b hb epsilon) b _ _ hb (Q'.le_of_lt hd)
          (hfloor i) (hfloor j) h)
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (tolerance_budget b hb epsilon)))
    exact ⟨step p q hh.2, step q p hh.1⟩

def value : CReal := CReal.ofQ'CauchySeq (term b hb hfloor) (reciprocalCauchy c b hb hfloor)

theorem value_approx (n : Nat) :
    (value c b hb hfloor).approx n =
      term b hb hfloor (CReal.QMhat _ (reciprocalCauchy c b hb hfloor) n) := rfl

theorem value_approx_pos (n : Nat) : (0 : Q') < (value c b hb hfloor).approx n :=
  term_pos b hb hfloor _

theorem value_approx_le (n : Nat) : (value c b hb hfloor).approx n ≤ Q'.recipPos b hb :=
  term_le b hb hfloor _

/-- An explicit upper bound on the original stream gives a reciprocal floor. -/
theorem value_approx_ge (B : Q') (hB : (0 : Q') < B) (hupper : ∀ n, r n ≤ B) (n : Nat) :
    Q'.recipPos B hB ≤ (value c b hb hfloor).approx n :=
  ArtanhMonotone.recipPos_antitone _ _ (Q'.pos_of_lt_of_le hb (hfloor _)) hB (hupper _)

theorem converges : CReal.ConvergesTo (fun n => CReal.ofQ' (term b hb hfloor n))
    (value c b hb hfloor) := CReal.convergesTo_ofQ'CauchySeq _ _

/-- The reciprocal is tied to the SAME original stream limit. -/
theorem mul_value : CReal.Equiv
    (CReal.mul (CReal.ofQ'CauchySeq r c) (value c b hb hfloor)) CReal.cone := by
  obtain ⟨B, hB, hbound⟩ := c.globalBound
  let R := Q'.recipPos b hb
  let cap := Q'.max' B R
  have hcap : (0 : Q') ≤ cap := Q'.le_trans' _ _ _ hB (Q'.le_max'_left _ _)
  have hmul : CReal.ConvergesTo
      (fun k => CReal.mul (CReal.ofQ' (r k)) (CReal.ofQ' (term b hb hfloor k)))
      (CReal.mul (CReal.ofQ'CauchySeq r c) (value c b hb hfloor)) := CReal.convergesTo_mul hcap
    (fun k _ => Q'.le_trans' _ _ _ (hbound k) (Q'.le_max'_left _ _))
    (fun n => Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (Q'.le_of_lt (value_approx_pos c b hb hfloor n)))))
        (value_approx_le c b hb hfloor n)) (Q'.le_max'_right _ _))
    (CReal.convergesTo_ofQ'CauchySeq r c) (converges c b hb hfloor)
  have hone : CReal.ConvergesTo (fun _ => CReal.cone)
      (CReal.mul (CReal.ofQ'CauchySeq r c) (value c b hb hfloor)) :=
    TrigAddCReal.convergesTo_congr_seq
      (fun n => SumOfSquares.Equiv_of_approx_eqv
        (fun _ => Q'.mul_recipPos_eqv (r n) (Q'.pos_of_lt_of_le hb (hfloor n)))) hmul
  exact CReal.Equiv_of_ofQ'_limit_close hone (CReal.convergesTo_const CReal.cone)
    (fun epsilon he => ⟨0, fun _ _ =>
      ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he), Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩⟩)

end YMGap.Continuum.PositiveRationalCauchyReciprocal

#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.term
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.term_pos
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.term_le
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.sensitivity
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.sensitivity_pos
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.tolerance
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.tolerance_pos
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.tolerance_budget
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.reciprocalCauchy
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.value
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.value_approx
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.value_approx_pos
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.value_approx_le
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.value_approx_ge
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.converges
#print axioms YMGap.Continuum.PositiveRationalCauchyReciprocal.mul_value
