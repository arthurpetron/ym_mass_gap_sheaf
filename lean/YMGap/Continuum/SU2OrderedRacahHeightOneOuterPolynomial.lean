/-
# The arbitrary-order outer polynomial at second coordinate two

At height one, the reduced exchange and lower adjacent carrier both contain
an outer transvectant with second monomial coordinate `2`.  Independently of
the contraction order, its defining factorial sum has exactly the first
three possible summands.  This removes the remaining opaque sum from those
two carriers without imposing the special shell `i=r+1`.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport

namespace YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantHighestWeightRowFormula
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneResidual
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport

local infix:50 " ≈ " => Q'.eqv

private theorem finSum_eqv_first_three (f : Nat → Q') : ∀ M,
    (∀ r, r < M + 3 → 3 ≤ r → f r ≈ 0) →
      finSum f (M + 3) ≈ (f 0 + f 1) + f 2
  | 0, _ => by
      change (((0 : Q') + f 0) + f 1) + f 2 ≈ (f 0 + f 1) + f 2
      exact Q'.add_eqv_congr_right _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_of_eq (Q'.zero_add' (f 0))))
  | M + 1, hzero => by
      change finSum f (M + 3) + f (M + 3) ≈ (f 0 + f 1) + f 2
      refine Q'.eqv_trans _ (((f 0 + f 1) + f 2) + 0) _
        (Q'.add_eqv_congr'
          (finSum_eqv_first_three f M (fun r hr h3 =>
            hzero r (by omega) h3))
          (hzero (M + 3) (by omega) (by omega))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' ((f 0 + f 1) + f 2))

private theorem second_two_term_zero_above
    (m n k i r : Nat) (hr : 3 ≤ r) :
    heightFactorialSummand m n k i 2 r ≈ 0 := by
  have hz : tvFallQ 2 r ≈ 0 := tvFallQ_eqv_zero_of_lt 2 r (by omega)
  let A := tvPhase r * tvBinomQ k r * tvFallQ i (k - r) *
    tvFallQ (m - i) r
  have h0 : A * tvFallQ 2 r ≈ 0 :=
    Q'.eqv_trans _ (A * 0) _
      (Q'.mul_eqv_congr_left A _ _ hz) (Q'.mul_zero_eqv A)
  unfold heightFactorialSummand
  exact Q'.eqv_trans _ (0 * tvFallQ (n - 2) (k - r)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) (Q'.zero_mul_eqv _)

/-- The explicit outer polynomial selected by second coordinate `2`. -/
def outerSecondTwoPolynomial (m n k i : Nat) : Q' :=
  (heightFactorialSummand m n k i 2 0 +
    heightFactorialSummand m n k i 2 1) +
    heightFactorialSummand m n k i 2 2

/-- **Exact outer height-one polynomial.**  For every contraction order at
least two, second coordinate `2` restricts the factorial row to the three
summands `r=0,1,2`. -/
theorem transvectFactorialCoeff_second_two_three_term
    (m n k i : Nat) (hk : 2 ≤ k) :
    transvectFactorialCoeff m n k i 2 ≈
      outerSecondTwoPolynomial m n k i := by
  unfold outerSecondTwoPolynomial
  unfold transvectFactorialCoeff
  have hlen : k + 1 = (k - 2) + 3 := by omega
  rw [hlen]
  apply finSum_eqv_first_three _ (k - 2)
  intro r hr h3
  exact second_two_term_zero_above m n k i r h3

/-- The reduced exchange outer row is now an explicit three-term
polynomial. -/
theorem reduced_height_one_outer_three_term {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i : Nat) (hr : 2 ≤ q.r) :
    transvectFactorialCoeff a q.intermediate q.r (i - 1) 2 ≈
      (heightFactorialSummand a q.intermediate q.r (i - 1) 2 0 +
        heightFactorialSummand a q.intermediate q.r (i - 1) 2 1) +
        heightFactorialSummand a q.intermediate q.r (i - 1) 2 2 :=
  transvectFactorialCoeff_second_two_three_term
    a q.intermediate q.r (i - 1) hr

/-- The lower adjacent outer row is likewise an explicit three-term
polynomial. -/
theorem lower_height_one_outer_three_term {a b c d : Nat}
    (qm : FixedRightCGChannel a b c d) (i : Nat) (hr : 2 ≤ qm.r) :
    transvectFactorialCoeff a qm.intermediate qm.r i 2 ≈
      (heightFactorialSummand a qm.intermediate qm.r i 2 0 +
        heightFactorialSummand a qm.intermediate qm.r i 2 1) +
        heightFactorialSummand a qm.intermediate qm.r i 2 2 :=
  transvectFactorialCoeff_second_two_three_term
    a qm.intermediate qm.r i hr

/-- Full polynomial transport for the new reduced exchange contribution. -/
theorem reduced_height_one_new_term_full_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpc : q.p + 2 ≤ c) (hr : 2 ≤ q.r) :
    heightOneReducedNewTerm q i j l ≈
      (heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l *
        heightTwoLeftPolynomial (c - 1) (q.p - 1) l) *
      outerSecondTwoPolynomial a q.intermediate q.r (i - 1) := by
  have hinner := reduced_height_one_new_term_polynomial
    q hp i j l hj hl hheight hpc
  have houter := reduced_height_one_outer_three_term q i hr
  exact Q'.eqv_trans _ _ _ hinner
    (Q'.mul_eqv_congr_left _ _ _ houter)

/-- Full polynomial transport for the reduced legacy contribution. -/
theorem reduced_height_one_legacy_term_full_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c)
    (hr : 2 ≤ q.r) :
    heightOneReducedLegacyTerm q i j l ≈
      (heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l *
        heightTwoLegacyPolynomial (b - 1) (c - 1) (q.p - 1) j l) *
      outerSecondTwoPolynomial a q.intermediate q.r (i - 1) := by
  have hinner := reduced_height_one_legacy_term_polynomial
    q hp i j l hj hl hheight hpb hpc
  have houter := reduced_height_one_outer_three_term q i hr
  exact Q'.eqv_trans _ _ _ hinner
    (Q'.mul_eqv_congr_left _ _ _ houter)

/-- Full polynomial transport for the new lower-carrier contribution. -/
theorem lower_height_one_new_term_full_polynomial {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpc : q.p + 1 ≤ c) (hr : 2 ≤ qm.r) :
    heightOneLowerNewTerm qm i j l ≈
      (heightTwoCommonFactor b c qm.p j l *
        heightTwoLeftPolynomial c qm.p l) *
      outerSecondTwoPolynomial a qm.intermediate qm.r i := by
  have hinner := lower_height_one_new_term_polynomial
    qm q hprev i j l hj hl hheight hpc
  have houter := lower_height_one_outer_three_term qm i hr
  exact Q'.eqv_trans _ _ _ hinner
    (Q'.mul_eqv_congr_left _ _ _ houter)

/-- Full polynomial transport for the lower legacy contribution. -/
theorem lower_height_one_legacy_term_full_polynomial {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c)
    (hr : 2 ≤ qm.r) :
    heightOneLowerLegacyTerm qm i j l ≈
      (heightTwoCommonFactor b c qm.p j l *
        heightTwoLegacyPolynomial b c qm.p j l) *
      outerSecondTwoPolynomial a qm.intermediate qm.r i := by
  have hinner := lower_height_one_legacy_term_polynomial
    qm q hprev i j l hj hl hheight hpb hpc
  have houter := lower_height_one_outer_three_term qm i hr
  exact Q'.eqv_trans _ _ _ hinner
    (Q'.mul_eqv_congr_left _ _ _ houter)

end YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.transvectFactorialCoeff_second_two_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.reduced_height_one_outer_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.lower_height_one_outer_three_term
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.reduced_height_one_new_term_full_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.reduced_height_one_legacy_term_full_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.lower_height_one_new_term_full_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial.lower_height_one_legacy_term_full_polynomial
