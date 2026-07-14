/-
# Propagating the complete height-one quadratic carrier

The legacy cancellation module factors the middle and final summands of a
two-above-lowest factorial row.  Here the new initial summand is factored as
the complementary pure quadratic, yielding the complete three-term row as
one common factorial carrier times an explicit quadratic polynomial.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation

namespace YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- The pure `l` part of the quadratic height-two row. -/
def heightTwoLeftPolynomial (n k l : Nat) : Q' :=
  tvBinomQ l (l - 2) * Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)

/-- The complete explicit quadratic carried by a two-above-lowest row. -/
def heightTwoFullPolynomial (m n k j l : Nat) : Q' :=
  heightTwoLeftPolynomial n k l + heightTwoLegacyPolynomial m n k j l

/-- The initial (`l-2`) height-two summand is the pure `l` term of the exact
quadratic carrier. -/
theorem height_two_initial_summand_closed
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) (hkn : k + 2 ≤ n) :
    heightFactorialSummand m n k j l (l - 2) ≈
      heightTwoCommonFactor m n k j l *
        heightTwoLeftPolynomial n k l := by
  have hcomp : k - (l - 2) = j := by omega
  have hcancel := tvBinomQ_mul_endpoint_factorials k (l - 2) (by omega)
  have hcancel' :
      tvBinomQ k (l - 2) * tvFallQ (l - 2) (l - 2) * tvFallQ j j ≈
        Q'.ofNat (tvFact k) := by
    simpa only [hcomp] using hcancel
  have hchoose0 := tvBinomQ_mul_fact_eq_fall l (l - 2) (by omega)
  have hlfact := tvFallQ_self_factorial (l - 2)
  have hchoose :
      tvFallQ l (l - 2) ≈
        tvBinomQ l (l - 2) * tvFallQ (l - 2) (l - 2) := by
    refine Q'.eqv_symm (Q'.eqv_trans _
      (tvBinomQ l (l - 2) * Q'.ofNat (tvFact (l - 2))) _ ?_ hchoose0)
    exact Q'.mul_eqv_congr_left _ _ _ hlfact
  have hnshift1 := tvFallQ_trailing_shift (n - l) (j - 2) (by omega)
  have hnshift1' :
      tvFallQ (n - l) (j - 2) * Q'.ofNat (n - k) ≈
        tvFallQ (n - l) (j - 1) := by
    simpa only [show n - l - (j - 2) = n - k by omega,
      show j - 2 + 1 = j - 1 by omega] using hnshift1
  have hnshift2 := tvFallQ_trailing_shift (n - l) (j - 1) (by omega)
  have hnshift2' :
      tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k - 1) ≈
        tvFallQ (n - l) j := by
    simpa only [show n - l - (j - 1) = n - k - 1 by omega,
      show j - 1 + 1 = j by omega] using hnshift2
  have hnshift :
      (tvFallQ (n - l) (j - 2) * Q'.ofNat (n - k)) *
          Q'.ofNat (n - k - 1) ≈ tvFallQ (n - l) j :=
    Q'.eqv_trans _
      (tvFallQ (n - l) (j - 1) * Q'.ofNat (n - k - 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hnshift1') hnshift2'
  unfold heightFactorialSummand
  rw [hcomp]
  refine Q'.eqv_trans _
    (tvPhase (l - 2) * tvBinomQ k (l - 2) * tvFallQ j j *
      tvFallQ (m - j) (l - 2) *
      (tvBinomQ l (l - 2) * tvFallQ (l - 2) (l - 2)) *
      ((tvFallQ (n - l) (j - 2) * Q'.ofNat (n - k)) *
        Q'.ofNat (n - k - 1))) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr (Q'.eqv_refl _) (Q'.eqv_refl _))
              (Q'.eqv_refl _))
            (Q'.eqv_refl _))
          hchoose)
        (Q'.eqv_symm hnshift)
  · unfold heightTwoCommonFactor heightTwoLeftPolynomial
    refine Q'.eqv_trans _
      ((tvPhase (l - 2) *
          (tvBinomQ k (l - 2) * tvFallQ (l - 2) (l - 2) *
            tvFallQ j j) *
          tvFallQ (m - j) (l - 2) * tvFallQ (n - l) (j - 2)) *
        (tvBinomQ l (l - 2) * Q'.ofNat (n - k) *
          Q'.ofNat (n - k - 1))) _ (by ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hcancel')))

/-- **Complete height-one carrier polynomial.**  Every supported row two
above lowest support is its common factorial carrier times the explicit
three-part quadratic `left + mixed + right`. -/
theorem transvectFactorialCoeff_two_above_lowest_closed
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hsum : j + l = k + 2) (hkm : k + 2 ≤ m) (hkn : k + 2 ≤ n) :
    transvectFactorialCoeff m n k j l ≈
      heightTwoCommonFactor m n k j l *
        heightTwoFullPolynomial m n k j l := by
  have hthree := transvectFactorialCoeff_two_above_lowest_three_term
    m n k j l hj hl hsum
  have hleft := height_two_initial_summand_closed
    m n k j l hj hl hsum hkn
  have hlegacy := height_two_legacy_pair_closed
    m n k j l hj hl hsum hkm hkn
  refine Q'.eqv_trans _ _ _ hthree ?_
  refine Q'.eqv_trans _
    (heightFactorialSummand m n k j l (l - 2) +
      (heightFactorialSummand m n k j l (l - 1) +
        heightFactorialSummand m n k j l l)) _
    (Q'.add_assoc_eqv
      (heightFactorialSummand m n k j l (l - 2))
      (heightFactorialSummand m n k j l (l - 1))
      (heightFactorialSummand m n k j l l)) ?_
  refine Q'.eqv_trans _
    (heightTwoCommonFactor m n k j l * heightTwoLeftPolynomial n k l +
      heightTwoCommonFactor m n k j l *
        heightTwoLegacyPolynomial m n k j l) _
    (Q'.add_eqv_congr' hleft hlegacy) ?_
  unfold heightTwoFullPolynomial
  exact Q'.eqv_symm (Q'.mul_add_eqv
    (heightTwoCommonFactor m n k j l)
    (heightTwoLeftPolynomial n k l)
    (heightTwoLegacyPolynomial m n k j l))

end YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation.height_two_initial_summand_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation.transvectFactorialCoeff_two_above_lowest_closed
