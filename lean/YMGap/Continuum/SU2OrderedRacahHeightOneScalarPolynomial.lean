/-
# Scalar polynomial for the height-one reduced exchange samples

The four reduced exchange samples at outer coordinates `2,1,1,0` are now
factored over one common inner factorial carrier.  This begins the final
finite scalar identity after the outer `2/1/0` common-factor alignment.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor

namespace YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- Common inner factorial carrier for all four reduced exchange samples. -/
def reducedHeightOneInnerBase {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  heightTwoCommonFactor (b - 1) (c - 1) (q.p - 1) j l

/-- Scalar of the coordinate-two reduced inner sample. -/
def reducedHeightOneInnerTwoScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  heightTwoFullPolynomial (b - 1) (c - 1) (q.p - 1) j l

/-- Scalar of the `(j,l-1)` coordinate-one reduced inner sample. -/
def reducedHeightOneInnerFirstOneScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  Q'.ofNat (c - l) *
    (Q'.ofNat (l - 1) * Q'.ofNat (c - q.p) +
      -(Q'.ofNat j * Q'.ofNat (b - q.p)))

/-- Scalar of the `(j-1,l)` coordinate-one reduced inner sample. -/
def reducedHeightOneInnerSecondOneScalar {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (j l : Nat) : Q' :=
  -(Q'.ofNat (b - j) *
    (Q'.ofNat l * Q'.ofNat (c - q.p) +
      -(Q'.ofNat (j - 1) * Q'.ofNat (b - q.p))))

/-- Scalar of the `(j-1,l-1)` coordinate-zero reduced inner sample. -/
def reducedHeightOneInnerZeroScalar (b c j l : Nat) : Q' :=
  -(Q'.ofNat (b - j) * Q'.ofNat (c - l))

/-- The coordinate-two sample is already in the common-base form. -/
theorem reduced_height_one_inner_two_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) j l ≈
      reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerTwoScalar q j l := by
  unfold reducedHeightOneInnerBase reducedHeightOneInnerTwoScalar
  exact transvectFactorialCoeff_two_above_lowest_closed
    (b - 1) (c - 1) (q.p - 1) j l hj hl
      (by omega) (by omega) (by omega)

/-- The first coordinate-one predecessor uses the same inner base; the
omitted leading factor is exactly `c-l`. -/
theorem reduced_height_one_inner_first_one_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) j (l - 1) ≈
      reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerFirstOneScalar q j l := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - 1 - j) (l - 2)
  let N := tvFallQ (c - 1 - l) (j - 2)
  let C := Q'.ofNat (c - l)
  let S := Q'.ofNat (l - 1) * Q'.ofNat (c - q.p) +
    -(Q'.ofNat j * Q'.ofNat (b - q.p))
  have hrow := transvectFactorialCoeff_one_above_lowest_closed
    (b - 1) (c - 1) (q.p - 1) j (l - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hn0 := tvFallQ_leading_shift (c - l) (j - 2)
  have hn : C * N ≈ tvFallQ (c - l) (j - 1) := by
    simpa only [C, N, show c - l - 1 = c - 1 - l by omega,
      show j - 2 + 1 = j - 1 by omega] using hn0
  refine Q'.eqv_trans _ ((P * K * M * tvFallQ (c - l) (j - 1)) * S) _
    (by
      simpa only [P, K, M, S,
        show l - 1 - 1 = l - 2 by omega,
        show b - 1 - j = b - 1 - j by rfl,
        show c - 1 - (l - 1) = c - l by omega,
        show (c - 1) - (q.p - 1) = c - q.p by omega,
        show (b - 1) - (q.p - 1) = b - q.p by omega] using hrow) ?_
  refine Q'.eqv_trans _ ((P * K * M * (C * N)) * S) _
    (Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_left (P * K * M) _ _ (Q'.eqv_symm hn))) ?_
  unfold reducedHeightOneInnerBase reducedHeightOneInnerFirstOneScalar
    heightTwoCommonFactor
  simp only [P, K, M, N, C, S]
  ring_qeqv

/-- The second coordinate-one predecessor uses the same base; its phase
shift supplies the displayed minus sign. -/
theorem reduced_height_one_inner_second_one_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1) (j - 1) l ≈
      reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerSecondOneScalar q j l := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - 1 - j) (l - 2)
  let N := tvFallQ (c - 1 - l) (j - 2)
  let B := Q'.ofNat (b - j)
  let S := Q'.ofNat l * Q'.ofNat (c - q.p) +
    -(Q'.ofNat (j - 1) * Q'.ofNat (b - q.p))
  have hrow := transvectFactorialCoeff_one_above_lowest_closed
    (b - 1) (c - 1) (q.p - 1) (j - 1) l
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hp0 := tvPhase_succ (l - 2)
  have hphase : tvPhase (l - 1) ≈ -P := by
    simpa only [P, show l - 2 + 1 = l - 1 by omega] using hp0
  have hm0 := tvFallQ_leading_shift (b - j) (l - 2)
  have hm : B * M ≈ tvFallQ (b - j) (l - 1) := by
    simpa only [B, M, show b - j - 1 = b - 1 - j by omega,
      show l - 2 + 1 = l - 1 by omega] using hm0
  refine Q'.eqv_trans _
    ((tvPhase (l - 1) * K * tvFallQ (b - j) (l - 1) * N) * S) _
    (by
      simpa only [K, N, S,
        show j - 1 - 1 = j - 2 by omega,
        show b - 1 - (j - 1) = b - j by omega,
        show (c - 1) - (q.p - 1) = c - q.p by omega,
        show (b - 1) - (q.p - 1) = b - q.p by omega] using hrow) ?_
  refine Q'.eqv_trans _ (((-P) * K * (B * M) * N) * S) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ S
      (Q'.mul_eqv_congr_right _ _ N
        (mul_eqv_congr
          (Q'.mul_eqv_congr_right _ _ K hphase) (Q'.eqv_symm hm)))
  · unfold reducedHeightOneInnerBase reducedHeightOneInnerSecondOneScalar
      heightTwoCommonFactor
    simp only [P, K, M, N, B, S]
    ring_qeqv

/-- The coordinate-zero predecessor also shares the base, with both omitted
leading factors and the same phase shift. -/
theorem reduced_height_one_inner_zero_at_common_base {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (hp : 0 < q.p)
    (j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l)
    (hheight : j + l = q.p + 1)
    (hpb : q.p + 2 ≤ b) (hpc : q.p + 2 ≤ c) :
    transvectFactorialCoeff (b - 1) (c - 1) (q.p - 1)
        (j - 1) (l - 1) ≈
      reducedHeightOneInnerBase q j l *
        reducedHeightOneInnerZeroScalar b c j l := by
  let P := tvPhase (l - 2)
  let K := Q'.ofNat (tvFact (q.p - 1))
  let M := tvFallQ (b - 1 - j) (l - 2)
  let N := tvFallQ (c - 1 - l) (j - 2)
  let B := Q'.ofNat (b - j)
  let C := Q'.ofNat (c - l)
  have hrow := transvectFactorialCoeff_lowest_row_closed
    (b - 1) (c - 1) (q.p - 1) (j - 1) (l - 1) (by omega)
  have hp0 := tvPhase_succ (l - 2)
  have hphase : tvPhase (l - 1) ≈ -P := by
    simpa only [P, show l - 2 + 1 = l - 1 by omega] using hp0
  have hm0 := tvFallQ_leading_shift (b - j) (l - 2)
  have hm : B * M ≈ tvFallQ (b - j) (l - 1) := by
    simpa only [B, M, show b - j - 1 = b - 1 - j by omega,
      show l - 2 + 1 = l - 1 by omega] using hm0
  have hn0 := tvFallQ_leading_shift (c - l) (j - 2)
  have hn : C * N ≈ tvFallQ (c - l) (j - 1) := by
    simpa only [C, N, show c - l - 1 = c - 1 - l by omega,
      show j - 2 + 1 = j - 1 by omega] using hn0
  refine Q'.eqv_trans _
    (tvPhase (l - 1) * K * tvFallQ (b - j) (l - 1) *
      tvFallQ (c - l) (j - 1)) _
    (by
      simpa only [K, show b - 1 - (j - 1) = b - j by omega,
        show c - 1 - (l - 1) = c - l by omega] using hrow) ?_
  refine Q'.eqv_trans _ (((-P) * K * (B * M)) * (C * N)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (Q'.mul_eqv_congr_right _ _ K hphase) (Q'.eqv_symm hm))
      (Q'.eqv_symm hn)
  · unfold reducedHeightOneInnerBase reducedHeightOneInnerZeroScalar
      heightTwoCommonFactor
    simp only [P, K, M, N, B, C]
    ring_qeqv

end YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial.reduced_height_one_inner_two_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial.reduced_height_one_inner_first_one_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial.reduced_height_one_inner_second_one_at_common_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneScalarPolynomial.reduced_height_one_inner_zero_at_common_base
