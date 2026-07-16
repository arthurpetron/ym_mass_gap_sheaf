/-
# Positive production scales for the lower-six E8/E9 envelopes

The coefficient identities clear by one exact common denominator.  This file
proves that denominator strictly positive on the production tail and records
the closed integer scale identity used to recombine the Taylor and Base parts.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopePositiveScale

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic

local infix:50 " ≈ " => Q'.eqv

private theorem rnqpow_pos {value : Q'} (hvalue : (0 : Q') < value) :
    ∀ exponent : Nat, (0 : Q') < RingNormaliser.qpow value exponent
  | 0 => by
      change (0 : Q') < 1
      decide
  | exponent + 1 => Q'.mul_pos (rnqpow_pos hvalue exponent) hvalue

private theorem rnqpow_two_eqv_mul (value : Q') :
    RingNormaliser.qpow value 2 ≈ value * value := by
  change ((1 : Q') * value) * value ≈ value * value
  exact Q'.mul_eqv_congr_right _ _ value (Q'.one_mul_eqv value)

private theorem denominator_square_sub_one_pos {D : Q'}
    (hD4 : Q'.ofNat 4 ≤ D) :
    (0 : Q') < RingNormaliser.qpow D 2 + -(1 : Q') := by
  have hD0 : (0 : Q') ≤ D :=
    Q'.le_trans' _ _ _ (by decide) hD4
  have hfirst : Q'.ofNat 4 * Q'.ofNat 4 ≤ Q'.ofNat 4 * D :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hD4 (by decide)
  have hsecond : Q'.ofNat 4 * D ≤ D * D :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hD4 hD0
  have h16mul : Q'.ofNat 16 ≤ D * D :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (by decide : (Q'.ofNat 16) ≈ Q'.ofNat 4 * Q'.ofNat 4))
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have h16 : Q'.ofNat 16 ≤ RingNormaliser.qpow D 2 :=
    Q'.le_trans' _ _ _ h16mul
      (Q'.ge_of_eqv (rnqpow_two_eqv_mul D))
  have h15 : Q'.ofNat 15 ≤
      RingNormaliser.qpow D 2 + -(1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (by decide : (Q'.ofNat 15) ≈ Q'.ofNat 16 + -(1 : Q')))
      (Q'.add_le_add_right _ _ (-(1 : Q')) h16)
  exact Q'.pos_of_lt_of_le (by decide) h15

theorem envelopeSemanticDenominatorValue_pos
    {k : Nat} (hk : 8189 ≤ k) :
    (0 : Q') <
      envelopeSemanticDenominatorValue (Q'.ofNat (k + 2)) := by
  let D := Q'.ofNat (k + 2)
  have hD4 : Q'.ofNat 4 ≤ D := by
    dsimp only [D]
    exact CReal.ofNat_le_ofNat (by omega)
  have hDpos : (0 : Q') < D :=
    Q'.pos_of_lt_of_le (by decide) hD4
  have hRpos : (0 : Q') < RingNormaliser.qpow D 2 + -(1 : Q') :=
    denominator_square_sub_one_pos hD4
  have hDsuccPos : (0 : Q') < D + (1 : Q') :=
    Q'.add_pos hDpos (by decide)
  unfold envelopeSemanticDenominatorValue envelopeSemanticCommonValue
  dsimp only [D] at hDpos hRpos hDsuccPos ⊢
  exact Q'.mul_pos (rnqpow_pos hDpos 18)
    (Q'.mul_pos (rnqpow_pos hRpos 4)
      (rnqpow_pos hDsuccPos 15))

/-- The generated Base row scale was chosen so that its product with the raw
assembly coefficient is exactly the square of the Taylor clearing constant. -/
theorem tailEnvelopeProductionScale_identity :
    Q'.ofNat 737280 * Q'.ofNat 178605 ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 := by
  decide

/-- Recombination algebra for the staged Taylor and Base evaluators.  The
only non-formal coefficient fact is the closed scale identity above. -/
theorem tailEnvelopeProduction_recombine (denominator taylor base : Q') :
    RingNormaliser.qpow (Q'.ofNat 362880) 2 *
          (denominator * taylor) +
        Q'.ofNat 737280 *
          (Q'.ofNat 178605 * (denominator * base)) ≈
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (denominator * (taylor + base)) := by
  let scale := RingNormaliser.qpow (Q'.ofNat 362880) 2
  have hbase :
      Q'.ofNat 737280 *
          (Q'.ofNat 178605 * (denominator * base)) ≈
        scale * (denominator * base) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 737280) (Q'.ofNat 178605)
          (denominator * base)))
      (Q'.mul_eqv_congr_right _ _ _
        tailEnvelopeProductionScale_identity)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ hbase) (by
      have hinner := Q'.mul_add_eqv denominator taylor base
      have houter := Q'.mul_eqv_congr_left scale _ _ hinner
      have hdistrib := Q'.mul_add_eqv scale
        (denominator * taylor) (denominator * base)
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _ houter hdistrib))

/-- Sign-safe cancellation of the Taylor clearing square and the common
denominator. -/
theorem envelope_nonnegative_of_production_product
    {denominator envelope : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hproduct : (0 : Q') ≤
      RingNormaliser.qpow (Q'.ofNat 362880) 2 *
        (denominator * envelope)) :
    (0 : Q') ≤ envelope := by
  let scale := RingNormaliser.qpow (Q'.ofNat 362880) 2
  have hscale : (0 : Q') < scale := by
    dsimp only [scale]
    have hconstant : (0 : Q') < Q'.ofNat 362880 := by
      simpa only [show 362879 + 1 = 362880 by decide] using
        Q'.ofNat_succ_pos 362879
    exact rnqpow_pos hconstant 2
  have hgrouped : (0 : Q') ≤ (scale * denominator) * envelope :=
    Q'.le_trans' _ _ _ hproduct
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.mul_assoc_eqv scale denominator envelope)))
  exact Q'.nonneg_of_mul_pos
    (Q'.mul_pos hscale hdenominator) hgrouped

#print axioms envelopeSemanticDenominatorValue_pos
#print axioms tailEnvelopeProductionScale_identity
#print axioms tailEnvelopeProduction_recombine
#print axioms envelope_nonnegative_of_production_product

end YMGap.Continuum.HarmonicLowerSixTailEnvelopePositiveScale
