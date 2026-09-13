/-
# Whole-polynomial comparison for the original finite Jacobi identity

The Gaussian factor absorbs the moving coefficient deficit:

  q^((r+1)^2) (q*q)^(N-r) = q^(2N+1) q^(r*r).

Thus the error of the ENTIRE finite polynomial, not only a fixed band of
coefficients, is at most C(q) q^(2N+1) on -1<=x<=1, where
C(q) = (2/(1-q*q)) (1+2/(1-q)). Every constant and cutoff is computed.
This is uniform in x on the stated interval, NOT uniform in q approaching
one. The differentiated identity and physical positivity remain separate.
-/

import YMGap.Continuum.FiniteJacobiIdentity
import YMGap.Continuum.FiniteJacobiWeightConvergence
import YMGap.Continuum.ChebyshevU
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.FiniteJacobiSeriesComparison

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteJacobiCoefficients
open YMGap.Continuum.FiniteJacobiIdentity
open YMGap.Continuum.FiniteJacobiWeightBounds
open YMGap.Continuum.FiniteJacobiWeightConvergence

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem neg_num_cast (a : Q') : (-a).num = -a.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem add_le {a b c d : Q'} (h : a ≤ b) (h' : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h) (Q'.add_le_add_left _ _ _ h')

private theorem sum_sub (a b : Nat → Q') (x : Q') (N : Nat) :
    FiniteSymmetricChebyshev.sum a x N + -FiniteSymmetricChebyshev.sum b x N
      ≈ FiniteSymmetricChebyshev.sum (fun j => a j + -b j) x N := by
  induction N with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      calc FiniteSymmetricChebyshev.sum a x (N + 1) + -FiniteSymmetricChebyshev.sum b x (N + 1)
          ≈ (FiniteSymmetricChebyshev.sum a x N + -FiniteSymmetricChebyshev.sum b x N)
            + (2 : Q') * (a (N + 1) + -b (N + 1)) * Cheb.T (N + 1) x := by
              rw [FiniteSymmetricChebyshev.sum, FiniteSymmetricChebyshev.sum]
              ring_qeqv
        _ ≈ FiniteSymmetricChebyshev.sum (fun j => a j + -b j) x (N + 1) :=
          Q'.add_eqv_congr_right _ _ _ ih

private theorem term_abs_le (a x : Q') (r : Nat)
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) :
    Q'.abs ((2 : Q') * a * Cheb.T (r + 1) x) ≤ (2 : Q') * Q'.abs a := by
  have hT := ChebU.Tabs_le_one r x hx1 hxm1
  have htwo : Q'.abs ((2 : Q') * a) ≤ (2 : Q') * Q'.abs a := by
    have h := ExpNeg.abs_mul_le (2 : Q') a
    rw [ExpNeg.abs_of_nonneg (by decide : (0 : Q') ≤ 2)] at h
    exact h
  exact Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.abs_le hT.1 hT.2) (Q'.abs_nonneg _))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) htwo))

private theorem sum_geometric_abs (a : Nat → Q') (q K x : Q')
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (M : Nat)
    (hzero : Q'.abs (a 0) ≤ K)
    (hnext : ∀ r, r < M → Q'.abs (a (r + 1)) ≤ K * q ^ r) :
    Q'.abs (FiniteSymmetricChebyshev.sum a x M)
      ≤ K + (2 : Q') * K * finSum (fun r => q ^ r) M := by
  induction M with
  | zero =>
      exact Q'.le_trans' _ _ _ hzero (Q'.ge_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
          (by rw [Q'.add_zero']; exact Q'.eqv_refl _)))
  | succ M ih =>
      have hs := ih (fun r hr => hnext r (by omega))
      have ht := Q'.le_trans' _ _ _ (term_abs_le (a (M + 1)) x M hx1 hxm1)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (hnext M (by omega))
          (by decide : (0 : Q') ≤ 2))
      exact Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
        (Q'.le_trans' _ _ _ (add_le hs ht) (Q'.le_of_eqv (by
          change (K + (2 : Q') * K * finSum (fun r => q ^ r) M)
              + (2 : Q') * (K * q ^ M)
            ≈ K + (2 : Q') * K * (finSum (fun r => q ^ r) M + q ^ M)
          ring_qeqv)))

/-- Bare symmetric theta polynomial, with the central one and factor two. -/
def bareTheta (q x : Q') (N : Nat) : Q' :=
  FiniteSymmetricChebyshev.sum (fun j => q ^ (j * j)) x N

/-- The signed difference of the ACTUAL finite and bare coefficients. -/
def coefficientError (q : Q') (N j : Nat) : Q' :=
  q ^ (j * j) * (centeredWeight (q * q) N j + -(1 : Q'))

theorem finiteJacobi_sub_bareTheta (q x : Q') (N : Nat) :
    finiteJacobi q x N + -bareTheta q x N
      ≈ FiniteSymmetricChebyshev.sum (coefficientError q N) x N := by
  apply Q'.eqv_trans _ _ _ (sum_sub _ _ x N)
  apply FiniteSymmetricChebyshev.sum_congr
  intro j _
  unfold coefficientError
  ring_qeqv

/-- The cutoff-dependent common factor left by Gaussian absorption. -/
def errorAmplitude (q : Q') (N : Nat) : Q' := lossScale (q * q) * amp q N

theorem errorAmplitude_nonnegative {q : Q'} (hq0 : (0 : Q') ≤ q) (N : Nat) :
    (0 : Q') ≤ errorAmplitude q N :=
  Q'.mul_nonneg _ _ (lossScale_nonnegative _) (Q'.pow_nonneg q hq0 _)

private theorem coefficientError_loss {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N j : Nat) (hj : j ≤ N) :
    Q'.abs (coefficientError q N j) ≤ q ^ (j * j) * lossBound (q * q) (N - j + 1) := by
  have hpow := Q'.pow_nonneg q (Q'.le_of_lt hq0) (j * j)
  have h := ExpNeg.abs_mul_le (q ^ (j * j)) (centeredWeight (q * q) N j + -(1 : Q'))
  rw [ExpNeg.abs_of_nonneg hpow] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (centeredWeight_abs_loss (HKPos.q_mul_pos hq0 hq0) (square_base_lt_one hq0 hq1) N j hj) hpow)

theorem coefficientError_zero_le {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N : Nat) :
    Q'.abs (coefficientError q N 0) ≤ errorAmplitude q N := by
  have he : q ^ (0 * 0) * lossBound (q * q) (N - 0 + 1)
      ≈ lossScale (q * q) * (q * q) ^ (N + 1) := by
    simp only [Nat.mul_zero, Q'.pow_zero, Nat.sub_zero]
    unfold lossBound HKConvGen.geoTailBase lossScale
    ring_qeqv
  have hp : (q * q) ^ (N + 1) ≤ amp q N := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (square_pow q _))
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) (by omega))
  exact Q'.le_trans' _ _ _ (coefficientError_loss hq0 hq1 N 0 (by omega))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (lossScale_nonnegative _)))

/-- The moving deficit leaves a summable Gaussian, with a common decay rate. -/
theorem coefficientError_succ_le_gaussian {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N r : Nat) (hr : r + 1 ≤ N) :
    Q'.abs (coefficientError q N (r + 1)) ≤ errorAmplitude q N * q ^ (r * r) := by
  have he : q ^ ((r + 1) * (r + 1)) * lossBound (q * q) (N - (r + 1) + 1)
      ≈ errorAmplitude q N * q ^ (r * r) := by
    rw [show N - (r + 1) + 1 = N - r by omega]
    calc q ^ ((r + 1) * (r + 1)) * lossBound (q * q) (N - r)
        ≈ lossScale (q * q) * (q ^ ((r + 1) * (r + 1)) * (q * q) ^ (N - r)) := by
          unfold lossBound HKConvGen.geoTailBase lossScale
          ring_qeqv
      _ ≈ lossScale (q * q) * (amp q N * q ^ (r * r)) :=
        Q'.mul_eqv_congr_left _ _ _ (lower_power q N r hr)
      _ ≈ errorAmplitude q N * q ^ (r * r) := by unfold errorAmplitude; ring_qeqv
  exact Q'.le_trans' _ _ _ (coefficientError_loss hq0 hq1 N (r + 1) hr) (Q'.le_of_eqv he)

theorem coefficientError_succ_le_geometric {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N r : Nat) (hr : r + 1 ≤ N) :
    Q'.abs (coefficientError q N (r + 1)) ≤ errorAmplitude q N * q ^ r := by
  have hr2 : r ≤ r * r := by
    cases r with
    | zero => decide
    | succ r => exact Nat.le_mul_of_pos_right _ (by omega)
  exact Q'.le_trans' _ _ _ (coefficientError_succ_le_gaussian hq0 hq1 N r hr)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) hr2)
      (errorAmplitude_nonnegative (Q'.le_of_lt hq0) N))

/-- Explicit q-dependent constant; no bound uniform as q approaches one. -/
def comparisonScale (q : Q') : Q' :=
  lossScale (q * q) * (1 + (2 : Q') * HKConv.divPos 1 (1 + -q))

theorem comparisonScale_nonnegative (q : Q') : (0 : Q') ≤ comparisonScale q :=
  Q'.mul_nonneg _ _ (lossScale_nonnegative _) (Q'.le_trans' _ _ _ Q'.zero_le_one
    (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (HKConv.divPos_nonneg Q'.zero_le_one))))

/-- Whole finite product versus bare theta polynomial, on the named interval. -/
theorem Ppart_sub_bareTheta_le {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    Q'.abs (ThetaConv.Ppart q x N + -bareTheta q x N)
      ≤ comparisonScale q * amp q N := by
  have he : ThetaConv.Ppart q x N + -bareTheta q x N
      ≈ FiniteSymmetricChebyshev.sum (coefficientError q N) x N :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Ppart_eq_finiteJacobi hq0 hq1 x N))
      (finiteJacobi_sub_bareTheta q x N)
  have hs := sum_geometric_abs (coefficientError q N) q (errorAmplitude q N) x hx1 hxm1 N
    (coefficientError_zero_le hq0 hq1 N)
    (fun r hr => coefficientError_succ_le_geometric hq0 hq1 N r (by omega))
  have hg := Q'.add_le_add_left (errorAmplitude q N) _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (HKConvGen.geom_series_le_base hq0 hq1 N)
      (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
        (errorAmplitude_nonnegative (Q'.le_of_lt hq0) N)))
  have hfinal : errorAmplitude q N
      + (2 : Q') * errorAmplitude q N * HKConv.divPos 1 (1 + -q)
      ≈ comparisonScale q * amp q N := by
    unfold comparisonScale errorAmplitude
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr he))
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ hg (Q'.le_of_eqv hfinal)))

/-- Tolerance for the power modulus, computed from the entire-series scale. -/
def comparisonTolerance (q ε : Q') : Q' := HKConv.divPos ε (comparisonScale q + 1)

theorem comparisonTolerance_pos (q : Q') {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < comparisonTolerance q ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem comparisonTolerance_budget (q : Q') {ε : Q'} (hε : (0 : Q') < ε) :
    comparisonScale q * comparisonTolerance q ε ≤ ε := by
  have hp : (0 : Q') < comparisonScale q + 1 := Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (comparisonScale_nonnegative q))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_lt (comparisonTolerance_pos q hε)))
      (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp))))

/-- Computed cutoff for the whole comparison; independent of x in [-1,1]. -/
def comparisonCutoff (q ε : Q') : Nat := HKConvGen.powBaseCutoff q (comparisonTolerance q ε)

theorem comparison_bound_le {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : comparisonCutoff q ε ≤ N) :
    comparisonScale q * amp q N ≤ ε := by
  have hp : amp q N ≤ comparisonTolerance q ε := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1)
      (show HKConvGen.powBaseCutoff q (comparisonTolerance q ε) ≤ 2 * N + 1 from by
        unfold comparisonCutoff at hN; omega))
    (HKConvGen.pow_base_le_cutoff hq0 hq1 (comparisonTolerance_pos q hε))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (comparisonScale_nonnegative q))
    (comparisonTolerance_budget q hε)

/-- The ORIGINAL full product and bare series approach each other with a
computed modulus, simultaneously for every point in the stated interval. -/
theorem Ppart_sub_bareTheta_close {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : comparisonCutoff q ε ≤ N) :
    Q'.abs (ThetaConv.Ppart q x N + -bareTheta q x N) ≤ ε :=
  Q'.le_trans' _ _ _ (Ppart_sub_bareTheta_le hq0 hq1 hx1 hxm1 N)
    (comparison_bound_le hq0 hq1 hε N hN)

end YMGap.Continuum.FiniteJacobiSeriesComparison

#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.bareTheta
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.coefficientError
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.finiteJacobi_sub_bareTheta
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.errorAmplitude
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.errorAmplitude_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.coefficientError_zero_le
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.coefficientError_succ_le_gaussian
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.coefficientError_succ_le_geometric
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonScale
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonScale_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.Ppart_sub_bareTheta_le
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonTolerance
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonTolerance_pos
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonTolerance_budget
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparisonCutoff
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.comparison_bound_le
#print axioms YMGap.Continuum.FiniteJacobiSeriesComparison.Ppart_sub_bareTheta_close
