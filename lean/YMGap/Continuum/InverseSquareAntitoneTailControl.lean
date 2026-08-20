/-
M4d -- representation-invariant antitone cutoff rate for inverse-square tails.

The legacy inverse-square `SummableDistortion` uses `epsilon.den` in one valid
tail modulus.  Since `Q'` is intentionally unreduced, equivalent positive
rationals can have different denominators, so that particular modulus is not
antitone in the rational order.  Constructive-real completion requires an
antitone outer rate.

This file builds a fresh rate

  ceil(A / epsilon),

which is invariant under rational equivalence at the order level.  The usual
telescoping bound `tail <= A/(N+B-1)` then proves every finite inverse-square
tail below `epsilon`.  No Yang--Mills step estimate is proved here.
-/

import YMGap.Continuum.ArtanhMonotone
import YMGap.Continuum.BernsteinStageData
import YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.InverseSquareAntitoneTailControl

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArtanhMonotone
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.InverseSquareMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.SemicircleConvClosed
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableInverseSquare

/-- `A/epsilon`, extended by zero outside the positive branch. -/
def scaledReciprocal (A epsilon : Q') : Q' :=
  if h : (0 : Q') < epsilon then A * Q'.recipPos epsilon h else 0

/-- The order-respecting inverse-square tail cutoff `ceil(A/epsilon)`. -/
def inverseSquareTailRate (A epsilon : Q') : Nat :=
  qCeilNat (scaledReciprocal A epsilon)

theorem scaledReciprocal_antitone (A : Q') (hA : (0 : Q') <= A)
    {delta epsilon : Q'} (hdelta : (0 : Q') < delta)
    (hde : delta <= epsilon) :
    scaledReciprocal A epsilon <= scaledReciprocal A delta := by
  have hepsilon : (0 : Q') < epsilon :=
    Q'.pos_of_lt_of_le hdelta hde
  unfold scaledReciprocal
  rw [dif_pos hepsilon, dif_pos hdelta]
  exact Q'.mul_le_mul_of_nonneg_left _ _ A
    (recipPos_antitone delta epsilon hdelta hepsilon hde) hA

/-- The ceiling cutoff is antitone in the requested tolerance. -/
theorem inverseSquareTailRate_antitone (A : Q') (hA : (0 : Q') <= A) :
    forall epsilon delta : Q', (0 : Q') < delta -> delta <= epsilon ->
      inverseSquareTailRate A epsilon <= inverseSquareTailRate A delta := by
  intro epsilon delta hdelta hde
  exact qCeilNat_mono (scaledReciprocal_antitone A hA hdelta hde)

/-- A positive natural embeds as a positive rational. -/
theorem ofNat_pos {n : Nat} (hn : 0 < n) : (0 : Q') < Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) <
    (Q'.ofNat n).num * (1 : Int)
  rw [Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  have hcast : (0 : Int) < (n : Int) := by exact_mod_cast hn
  simpa only [Int.zero_mul, Int.mul_one] using hcast

/-- The telescoping potential is the reciprocal of its natural denominator. -/
theorem pot_eqv_recipOfNat (B : Nat) (hB : 2 <= B) (start : Nat) :
    (pot B hB start).eqv
      (Q'.recipPos (Q'.ofNat (start + B - 1))
        (ofNat_pos (by omega))) := by
  show (unit (start + B - 1) (by omega)).eqv
    (Q'.recipPos (Q'.ofNat (start + B - 1)) (ofNat_pos (by omega)))
  show (unit (start + B - 1) (by omega)).num *
      ((Q'.recipPos (Q'.ofNat (start + B - 1))
        (ofNat_pos (by omega))).den : Int) =
    (Q'.recipPos (Q'.ofNat (start + B - 1))
      (ofNat_pos (by omega))).num *
      ((unit (start + B - 1) (by omega)).den : Int)
  rw [unit_num, unit_den, Q'.recipPos_num, Q'.recipPos_den]
  rfl

/-- Past `ceil(A/epsilon)`, the scaled inverse-square potential is below
`epsilon`. -/
theorem scaled_pot_le_of_tailRate
    (B : Nat) (hB : 2 <= B) (A : Q') (_hA : (0 : Q') <= A)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (start : Nat) (hstart : inverseSquareTailRate A epsilon <= start) :
    A * pot B hB start <= epsilon := by
  have hceil : A * Q'.recipPos epsilon hepsilon <=
      Q'.ofNat (inverseSquareTailRate A epsilon) := by
    unfold inverseSquareTailRate scaledReciprocal
    rw [dif_pos hepsilon]
    exact q_le_qCeilNat (A * Q'.recipPos epsilon hepsilon)
  have hrateStart : Q'.ofNat (inverseSquareTailRate A epsilon) <=
      Q'.ofNat start :=
    CReal.ofNat_le_ofNat hstart
  have hquotStart : A * Q'.recipPos epsilon hepsilon <=
      Q'.ofNat start :=
    Q'.le_trans' _ _ _ hceil hrateStart
  have hscaled :
      epsilon * (A * Q'.recipPos epsilon hepsilon) <=
        epsilon * Q'.ofNat start :=
    Q'.mul_le_mul_of_nonneg_left _ _ epsilon hquotStart
      (Q'.le_of_lt hepsilon)
  have hcollapse :
      (epsilon * (A * Q'.recipPos epsilon hepsilon)).eqv A := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv epsilon A
        (Q'.recipPos epsilon hepsilon))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (epsilon * A) (A * epsilon)
        (Q'.recipPos epsilon hepsilon) (Q'.mul_comm_eqv epsilon A)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv A epsilon (Q'.recipPos epsilon hepsilon)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left A _ _
        (Q'.mul_recipPos_eqv epsilon hepsilon)) ?_
    exact Q'.mul_one_eqv A
  have hAstart : A <= epsilon * Q'.ofNat start :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hscaled
  have hstartDen : Q'.ofNat start <= Q'.ofNat (start + B - 1) :=
    CReal.ofNat_le_ofNat (by omega)
  have hscaledDen : epsilon * Q'.ofNat start <=
      epsilon * Q'.ofNat (start + B - 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ epsilon hstartDen
      (Q'.le_of_lt hepsilon)
  have hAden : A <= epsilon * Q'.ofNat (start + B - 1) :=
    Q'.le_trans' _ _ _ hAstart hscaledDen
  have hdiv :
      Q'.divPos A (Q'.ofNat (start + B - 1)) (ofNat_pos (by omega)) <=
        epsilon :=
    Q'.divPos_le_of_le_mul A (Q'.ofNat (start + B - 1))
      (ofNat_pos (by omega)) hAden
  have heq : (A * pot B hB start).eqv
      (Q'.divPos A (Q'.ofNat (start + B - 1))
        (ofNat_pos (by omega))) := by
    unfold Q'.divPos
    exact Q'.mul_eqv_congr_left A _ _ (pot_eqv_recipOfNat B hB start)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hdiv

/-- Any nonnegative rational sequence with a pointwise inverse-square majorant
has a representation-invariant antitone tail control.  This is the reusable
analytic core; Yang--Mills loss flows are only one specialization. -/
def inverseSquareTermTailControl
    (term : Nat -> Q')
    (offset : Nat) (offset_at_least_two : 2 <= offset)
    (coefficient : Q') (coefficient_nonnegative : (0 : Q') <= coefficient)
    (term_le : forall k : Nat,
      term k <= coefficient * invSqTerm offset offset_at_least_two k) :
    AntitoneTailControl term where
  tailRate := inverseSquareTailRate coefficient
  tailRate_antitone :=
    inverseSquareTailRate_antitone coefficient coefficient_nonnegative
  tailBound := by
    intro epsilon hepsilon start hstart length
    rw [finSum_shift_eq_tailSum]
    exact Q'.le_trans' _ _ _
      (summableBound_of_invSq offset offset_at_least_two
        coefficient coefficient_nonnegative term term_le start length)
      (scaled_pot_le_of_tailRate
        offset offset_at_least_two coefficient coefficient_nonnegative
        epsilon hepsilon start hstart)

/-- Any inverse-square controlled normalized loss has a representation-
invariant antitone tail control. -/
def inverseSquareTailControl
    {flow : MassNormalizedLossFlow}
    (control : InverseSquareRateLossControl flow) :
    AntitoneTailControl flow.rateLoss :=
  inverseSquareTermTailControl flow.rateLoss
    control.offset control.offset_at_least_two
    control.coefficient control.coefficient_nonnegative control.rateLoss_le

end YMGap.Continuum.InverseSquareAntitoneTailControl

#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.scaledReciprocal_antitone
#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.inverseSquareTailRate_antitone
#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.pot_eqv_recipOfNat
#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.scaled_pot_le_of_tailRate
#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.inverseSquareTermTailControl
#print axioms YMGap.Continuum.InverseSquareAntitoneTailControl.inverseSquareTailControl
