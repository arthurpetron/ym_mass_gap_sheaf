/-
# Transporting the height-one quadratic into correction carriers

The complete two-above-lowest polynomial is now specialized to the reduced
exchange channel and its lower adjacent carrier.  These are the two places
where the new `l-2` term enters the Omega correction.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation

namespace YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneResidual
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation

local infix:50 " ≈ " => Q'.eqv

/-- The reduced inner exchange row is the complete height-two quadratic in
the strict second interior. -/
theorem reduced_height_one_inner_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) j l ≈
      heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l *
        heightTwoFullPolynomial (b - 1) (c - 1) (q.p - 1) j l := by
  apply transvectFactorialCoeff_two_above_lowest_closed
    (b - 1) (c - 1) (q.p - 1) j l hj hl
  · omega
  · omega
  · omega

/-- The lower adjacent inner row carries the same quadratic mechanism with
its unreduced labels. -/
theorem lower_height_one_inner_polynomial {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c) :
    transvectFactorialCoeff b c qm.p j l ≈
      heightTwoCommonFactor b c qm.p j l *
        heightTwoFullPolynomial b c qm.p j l := by
  apply transvectFactorialCoeff_two_above_lowest_closed
    b c qm.p j l hj hl
  · omega
  · omega
  · omega

/-- The new reduced exchange term is its pure-left quadratic times the
unchanged outer row. -/
theorem reduced_height_one_new_term_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) (hpc : q.p + 2 ≤ c) :
    heightOneReducedNewTerm q i j l ≈
      (heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l *
        heightTwoLeftPolynomial (c - 1) (q.p - 1) l) *
      transvectFactorialCoeff a q.intermediate q.r (i - 1) 2 := by
  have hnew := height_two_initial_summand_closed
    (b - 1) (c - 1) (q.p - 1) j l hj hl (by omega) (by omega)
  unfold heightOneReducedNewTerm
  exact Q'.mul_eqv_congr_right _ _ _ hnew

/-- The reduced legacy pair is its mixed-plus-right quadratic times the
unchanged outer row. -/
theorem reduced_height_one_legacy_term_polynomial {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    heightOneReducedLegacyTerm q i j l ≈
      (heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l *
        heightTwoLegacyPolynomial (b - 1) (c - 1) (q.p - 1) j l) *
      transvectFactorialCoeff a q.intermediate q.r (i - 1) 2 := by
  have hlegacy := height_two_legacy_pair_closed
    (b - 1) (c - 1) (q.p - 1) j l hj hl
      (by omega) (by omega) (by omega)
  unfold heightOneReducedLegacyTerm
  exact Q'.mul_eqv_congr_right _ _ _ hlegacy

/-- The new lower-carrier term is its pure-left quadratic times its outer
row. -/
theorem lower_height_one_new_term_polynomial {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1) (hpc : q.p + 1 ≤ c) :
    heightOneLowerNewTerm qm i j l ≈
      (heightTwoCommonFactor b c qm.p j l *
        heightTwoLeftPolynomial c qm.p l) *
      transvectFactorialCoeff a qm.intermediate qm.r i 2 := by
  have hnew := height_two_initial_summand_closed
    b c qm.p j l hj hl (by omega) (by omega)
  unfold heightOneLowerNewTerm
  exact Q'.mul_eqv_congr_right _ _ _ hnew

/-- The lower legacy pair is its mixed-plus-right quadratic times its outer
row. -/
theorem lower_height_one_legacy_term_polynomial {a b c d : Nat}
    (qm q : FixedRightCGChannel a b c d)
    (hprev : q.p = qm.p + 1)
    (i j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 1 ≤ b) (hpc : q.p + 1 ≤ c) :
    heightOneLowerLegacyTerm qm i j l ≈
      (heightTwoCommonFactor b c qm.p j l *
        heightTwoLegacyPolynomial b c qm.p j l) *
      transvectFactorialCoeff a qm.intermediate qm.r i 2 := by
  have hlegacy := height_two_legacy_pair_closed
    b c qm.p j l hj hl (by omega) (by omega) (by omega)
  unfold heightOneLowerLegacyTerm
  exact Q'.mul_eqv_congr_right _ _ _ hlegacy

end YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.reduced_height_one_inner_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.lower_height_one_inner_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.reduced_height_one_new_term_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.reduced_height_one_legacy_term_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.lower_height_one_new_term_polynomial
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialTransport.lower_height_one_legacy_term_polynomial
