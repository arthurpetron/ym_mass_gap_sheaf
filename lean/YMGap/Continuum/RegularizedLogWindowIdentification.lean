/-
# Identification with the actual directly windowed scalar logarithm

The regularized-series value is identified with -x*logRat(x) on [1/2,1]
using a finite coefficient comparison, not a supplied logarithm law.
The original p_n approximants are retained: their explicit uniform tail
connects p_n to p_(2n), and the computed polynomial-geometric cutoff controls
the latter's comparison with the actual artanh approximant at n.

Both the equality cutoff and the input-value regularity are recoverable data.
Computed binary range reduction outside this window remains separate. This
is scalar entropy-series identification, not an original two-time response
bound, spacing-uniform estimate, or physical Hamiltonian gap.
-/

import YMGap.Continuum.RegularizedLogArtanhFiniteComparison
import YMGap.Continuum.RegularizedLogRationalAlgebra
import YMGap.Continuum.PolynomialGeometricDecay

namespace YMGap.Continuum.RegularizedLogWindowIdentification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RegularizedLogPolynomial
open YMGap.Continuum.RegularizedLogRationalAlgebra (value)
open YMGap.Continuum.PolynomialGeometricDecay (polynomialCutoff polynomial_bound)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def comparisonRate : Q' := Q'.mkPos 5 6 (by decide)
def comparisonAmplitude : Q' := Q'.mkPos 1 6 (by decide)

/-- One cutoff for the original-series tail and the finite artanh comparison. -/
def identificationRate (epsilon : Q') : Nat :=
  max (modulus (HalfPow.half*epsilon))
    (polynomialCutoff comparisonRate comparisonAmplitude 1 (HalfPow.half*epsilon)+1)

private theorem split_error {A B : Q'} {epsilon : Q'}
    (he : (0 : Q') < epsilon)
    (hA : A ≤ B+HalfPow.half*epsilon) : A ≤ B+epsilon := by
  have hhalf := ExpNeg.half_mul_pos epsilon he
  have hsum := Q'.add_le_self_of_nonneg (B+HalfPow.half*epsilon)
    (HalfPow.half*epsilon) (Q'.le_of_lt hhalf)
  have hpin : (B+HalfPow.half*epsilon)+HalfPow.half*epsilon ≈ B+epsilon :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hpin))

/-- Actual approximation streams, with the equality cutoff as data above. -/
theorem value_logRat_approx (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (hhalf : HalfPow.half ≤ x)
    (hm1 : (0 : Q') < x+1)
    (hyb : Q'.abs (CRealLog.yOf x hm1) ≤ CRealLog.recipOdd 1)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : identificationRate epsilon ≤ n) :
    (value x hx0 hx1).approx n ≤
      (CReal.neg (CReal.mul (CReal.ofQ' x) (CRealLog.logRat x hm1 hyb))).approx n + epsilon ∧
    (CReal.neg (CReal.mul (CReal.ofQ' x) (CRealLog.logRat x hm1 hyb))).approx n ≤
      (value x hx0 hx1).approx n + epsilon := by
  have hhalfE := ExpNeg.half_mul_pos epsilon he
  have ht : modulus (HalfPow.half*epsilon) ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hg : polynomialCutoff comparisonRate comparisonAmplitude 1
      (HalfPow.half*epsilon)+1 ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hnpos : 0 < n := by omega
  have hindex : polynomialCutoff comparisonRate comparisonAmplitude 1
      (HalfPow.half*epsilon) ≤ 2*n-1 := by omega
  have hexponent : (2*n-1+1)^1 = 2*n := by simp only [Nat.pow_one]; omega
  have hsmall := polynomial_bound (by decide : (0 : Q') ≤ comparisonRate)
    (by decide : comparisonRate < (1 : Q'))
    (by decide : (0 : Q') ≤ comparisonAmplitude) hhalfE 1 (2*n-1) hindex
  rw [hexponent] at hsmall
  have hfinite := RegularizedLogArtanhFiniteComparison.partial_logRat_error
    x hx0 hx1 hhalf hm1 hyb n hnpos
  have habs : Q'.abs (partialSum x (2*n)+x*((CRealLog.logRat x hm1 hyb).approx n)) ≤
      HalfPow.half*epsilon := Q'.le_trans' _ _ _ hfinite hsmall
  let L := x*((CRealLog.logRat x hm1 hyb).approx n)
  have hforward : partialSum x (2*n) ≤ -L+HalfPow.half*epsilon := by
    apply CReal.le_add_of_sub_le
    have hneg : partialSum x (2*n)+ -(-L) ≈ partialSum x (2*n)+L :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv L)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hneg)
      (Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs)
  have hbackward : -L ≤ partialSum x (2*n)+HalfPow.half*epsilon := by
    apply CReal.le_add_of_sub_le
    have hpin : -L + -(partialSum x (2*n)) ≈ -(partialSum x (2*n)+L) :=
      poly_identity_of_normal_eq
        (.add (.neg (.var 0)) (.neg (.var 1)))
        (.neg (.add (.var 1) (.var 0))) (by decide)
        (fun | 0 => L | _ => partialSum x (2*n))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) habs)
  have hn2 : n ≤ 2*n := by omega
  have hinv : Q'.invSucc n ≤ HalfPow.half*epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le ht)
      (HalfPow.invSucc_den_le _ hhalfE)
  have htail := Q'.le_trans' _ _ _ (partial_tail x hx0 hx1 hn2)
    (Q'.add_le_add_left _ _ _ hinv)
  refine ⟨split_error he
    (Q'.le_trans' _ _ _ (partial_mono x hx0 hx1 hn2) hforward), ?_⟩
  have hjoin := Q'.le_trans' _ _ _ hbackward
    (Q'.add_le_add_right _ _ (HalfPow.half*epsilon) htail)
  exact Q'.le_trans' _ _ _ hjoin (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))))

/-- No freely chosen logarithm scale enters this actual direct-window pin. -/
theorem value_logRat (x : Q')
    (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1) (hhalf : HalfPow.half ≤ x)
    (hm1 : (0 : Q') < x+1)
    (hyb : Q'.abs (CRealLog.yOf x hm1) ≤ CRealLog.recipOdd 1) :
    CReal.Equiv (value x hx0 hx1)
      (CReal.neg (CReal.mul (CReal.ofQ' x) (CRealLog.logRat x hm1 hyb))) :=
  fun epsilon he => ⟨identificationRate epsilon,
    fun n hn => value_logRat_approx x hx0 hx1 hhalf hm1 hyb epsilon he n hn⟩

/-- The halving constant is pinned to the actual artanh-defined log2, not
freely chosen as a range-reduction input. -/
theorem value_half_log2 :
    CReal.Equiv (value HalfPow.half HalfPow.half_nonneg (by decide))
      (CReal.mul (CReal.ofQ' HalfPow.half) CRealLog.log2) := by
  have hwindow := value_logRat HalfPow.half HalfPow.half_nonneg
    (by decide) (Q'.le_refl' _) CRealLogOddness.oneHalf_plus_one_pos
    CRealLogOddness.yOf_oneHalf_window
  refine CReal.Equiv.trans hwindow (SumOfSquares.Equiv_of_approx_eqv ?_)
  intro n
  have hpin := Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _
    (CRealLogOddness.logRat_oneHalf_approx_eqv_neg_log2_approx n))
  exact Q'.eqv_trans _ _ _ hpin
    (poly_identity_of_normal_eq (.neg (.mul (.var 0) (.neg (.var 1))))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => HalfPow.half | _ => CRealLog.log2.approx n))

end YMGap.Continuum.RegularizedLogWindowIdentification

#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.comparisonRate
#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.comparisonAmplitude
#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.identificationRate
#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.value_logRat_approx
#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.value_logRat
#print axioms YMGap.Continuum.RegularizedLogWindowIdentification.value_half_log2
