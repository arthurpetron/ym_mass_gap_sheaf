/-
# Quantitative control of the finite differentiated Jacobi identity

Gaussian absorption of the actual coefficient deficit leaves
(r+1)^2 q^(r*r). The shifted quadratic Gaussian is summable with an explicit
q-dependent constant. The resulting derivative comparison is on [-1,1],
including both endpoints; it does not posit off-interval convergence.
-/

import YMGap.Continuum.FiniteJacobiDerivativeIdentity
import YMGap.Continuum.FiniteJacobiSeriesComparison

namespace YMGap.Continuum.FiniteJacobiDerivativeComparison

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.FiniteSymmetricChebyshevDerivative
open YMGap.Continuum.FiniteJacobiDerivativeIdentity
open YMGap.Continuum.FiniteJacobiSeriesComparison
open YMGap.Continuum.FiniteJacobiWeightConvergence
open YMGap.Continuum.FiniteJacobiCoefficients
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.ChebTFwdRatioClose (Lcoef)

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

instance : Trans (α := Q') LE.le LE.le LE.le where
  trans h₁ h₂ := Q'.le_trans' _ _ _ h₁ h₂

private theorem neg_num_cast (a : Q') : (-a).num = -a.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

/-- The shifted Gaussian constant: 1 + 4*Cmaj(q)/q, all parameters exposed. -/
def shiftedGaussianScale (q : Q') : Q' := 1 + (4 : Q') * HKConv.divPos (JTPIdentity.Cmaj q) q

theorem one_le_shiftedGaussianScale {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (1 : Q') ≤ shiftedGaussianScale q :=
  Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 4)
    (HKConv.divPos_nonneg (JTPIdentity.Cmaj_nonneg hq0 hq1)))

theorem shiftedGaussianScale_nonnegative {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (0 : Q') ≤ shiftedGaussianScale q :=
  Q'.le_trans' _ _ _ Q'.zero_le_one (one_le_shiftedGaussianScale hq0 hq1)

private theorem successor_square_le_four (n : Nat) :
    Q'.ofNat (n + 2) * Q'.ofNat (n + 2)
      ≤ (4 : Q') * (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) := by
  have hn : (n + 2) * (n + 2) ≤ 4 * ((n + 1) * (n + 1)) := by
    have h := Nat.mul_self_le_mul_self (show n + 2 ≤ 2 * (n + 1) by omega)
    have he : (2 * (n + 1)) * (2 * (n + 1)) = 4 * ((n + 1) * (n + 1)) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm (n + 1) 2 (n + 1), ← Nat.mul_assoc]
    rw [he] at h
    exact h
  change (((n + 2 : Nat) : Int) * ((n + 2 : Nat) : Int)) * 1
    ≤ (4 * (((n + 1 : Nat) : Int) * ((n + 1 : Nat) : Int))) * 1
  simp only [Int.mul_one]
  exact_mod_cast hn

/-- The shifted quadratic Gaussian has a geometric majorant at every index. -/
theorem shiftedGaussian_le {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (r : Nat) :
    (Q'.ofNat (r + 1) * Q'.ofNat (r + 1)) * q ^ (r * r)
      ≤ shiftedGaussianScale q * q ^ r := by
  cases r with
  | zero =>
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide :
        (Q'.ofNat (0 + 1) * Q'.ofNat (0 + 1)) * (1 : Q') ≈ (1 : Q')))
        (Q'.le_trans' _ _ _ (one_le_shiftedGaussianScale hq0 hq1) (Q'.ge_of_eqv (Q'.mul_one_eqv _)))
  | succ n =>
      have he : (JTPIdentity.Cmaj q * q ^ n)
          ≈ HKConv.divPos (JTPIdentity.Cmaj q) q * q ^ (n + 1) := by
        calc JTPIdentity.Cmaj q * q ^ n
            ≈ (HKConv.divPos (JTPIdentity.Cmaj q) q * q) * q ^ n :=
              Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hq0)))
          _ ≈ HKConv.divPos (JTPIdentity.Cmaj q) q * q ^ (n + 1) := Q'.mul_assoc_eqv _ _ _
      have hscale : (4 : Q') * HKConv.divPos (JTPIdentity.Cmaj q) q ≤ shiftedGaussianScale q :=
        Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
      calc (Q'.ofNat (n + 1 + 1) * Q'.ofNat (n + 1 + 1)) * q ^ ((n + 1) * (n + 1))
          ≤ ((4 : Q') * (Q'.ofNat (n + 1) * Q'.ofNat (n + 1))) * q ^ ((n + 1) * (n + 1)) :=
            Q'.mul_le_mul_of_nonneg_right _ _ _ (successor_square_le_four n) (Q'.pow_nonneg q (Q'.le_of_lt hq0) _)
        _ ≤ (4 : Q') * ((Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * q ^ ((n + 1) * (n + 1))) :=
          Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)
        _ ≤ (4 : Q') * (JTPIdentity.Cmaj q * q ^ n) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ (JTPIdentity.dTermMaj_le (x := (0 : Q')) hq0 hq1 n)
            (by decide : (0 : Q') ≤ 4)
        _ ≤ ((4 : Q') * HKConv.divPos (JTPIdentity.Cmaj q) q) * q ^ (n + 1) :=
          Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ he)
            (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        _ ≤ shiftedGaussianScale q * q ^ (n + 1) :=
          Q'.mul_le_mul_of_nonneg_right _ _ _ hscale (Q'.pow_nonneg q (Q'.le_of_lt hq0) _)

private theorem abs_mul_bound {a b A B : Q'} (ha : Q'.abs a ≤ A) (hb : Q'.abs b ≤ B) :
    Q'.abs (a * b) ≤ A * B :=
  Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a b)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (Q'.le_trans' _ _ _ (Q'.abs_nonneg _) ha)))

theorem Lcoef_abs_le (x : Q') (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (r : Nat) :
    Q'.abs (Lcoef x (r + 1)) ≤ Q'.ofNat (r + 1) * Q'.ofNat (r + 1) := by
  have hU := ChebU.absU_le r x hx1 hxm1
  apply abs_mul_bound _ (Q'.abs_le hU.2 hU.1)
  rw [ExpNeg.abs_of_nonneg (JTPIdentity.ofNat_nonneg _)]; exact Q'.le_refl' _

private theorem dsum_sub (a b : Nat → Q') (x : Q') (M : Nat) :
    dsum a x M + -dsum b x M ≈ dsum (fun j => a j + -b j) x M := by
  induction M with
  | zero => change ((0 : Q') + -0) ≈ (0 : Q'); decide
  | succ M ih =>
      calc dsum a x (M + 1) + -dsum b x (M + 1)
          ≈ (dsum a x M + -dsum b x M)
            + (2 : Q') * (a (M + 1) + -b (M + 1)) * Lcoef x (M + 1) := by
              rw [dsum, dsum]; ring_qeqv
        _ ≈ dsum (fun j => a j + -b j) x (M + 1) := Q'.add_eqv_congr_right _ _ _ ih

theorem dsum_bare_eq_two_dPartial (q x : Q') (N : Nat) :
    dsum (fun j => q ^ (j * j)) x N ≈ (2 : Q') * JTPIdentity.dPartial q x N := by
  calc dsum (fun j => q ^ (j * j)) x N
      ≈ dsum (fun j => q ^ (j * j) * 1) x N :=
        dsum_congr _ _ x N (fun j _ => Q'.eqv_symm (Q'.mul_one_eqv _))
    _ ≈ (2 : Q') * finSum (fun r => (1 : Q') * JTPIdentity.dTerm q x r) N :=
      dsum_eq_two_weighted_dPartial q x (fun _ => 1) N
    _ ≈ (2 : Q') * JTPIdentity.dPartial q x N :=
      Q'.mul_eqv_congr_left _ _ _ (finSum_eqv_congr _ _ (fun _ => Q'.one_mul_eqv _) N)

/-- The actual finite derivative error, before any estimate. -/
theorem fullProdDx_sub_two_dPartial_eq {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    JTPFullProductDerivativeNormalization.fullProdDx q x N + -((2 : Q') * JTPIdentity.dPartial q x N)
      ≈ dsum (coefficientError q N) x N := by
  calc JTPFullProductDerivativeNormalization.fullProdDx q x N + -((2 : Q') * JTPIdentity.dPartial q x N)
      ≈ finiteJacobiDerivative q x N + -dsum (fun j => q ^ (j * j)) x N :=
        Cheb.add_eqv_congr _ _ _ _ (fullProdDx_eq_finiteJacobiDerivative hq0 hq1 hxm1 N)
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (dsum_bare_eq_two_dPartial q x N)))
    _ ≈ dsum (fun j => q ^ (j * j) * centeredWeight (q * q) N j + -(q ^ (j * j))) x N :=
      dsum_sub _ _ x N
    _ ≈ dsum (coefficientError q N) x N := by
      apply dsum_congr
      intro j _
      unfold coefficientError
      ring_qeqv

private theorem dsum_abs_le_sum (a : Nat → Q') (q K x : Q') (M : Nat)
    (h : ∀ r, r < M → Q'.abs ((2 : Q') * a (r + 1) * Lcoef x (r + 1)) ≤ K * q ^ r) :
    Q'.abs (dsum a x M) ≤ K * finSum (fun r => q ^ r) M := by
  induction M with
  | zero => exact Q'.ge_of_eqv (Q'.mul_zero_eqv K)
  | succ M ih =>
      exact Q'.le_trans' _ _ _ (Q'.abs_add_le' _ _)
        (Q'.le_trans' _ _ _ (Q'.add_le_add (ih (fun r hr => h r (by omega))) (h M (by omega)))
          (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _)))

theorem derivativeError_term_le {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N r : Nat) (hr : r + 1 ≤ N) :
    Q'.abs ((2 : Q') * coefficientError q N (r + 1) * Lcoef x (r + 1))
      ≤ ((2 : Q') * errorAmplitude q N * shiftedGaussianScale q) * q ^ r := by
  have h := abs_mul_bound
    (abs_mul_bound (by decide : Q'.abs (2 : Q') ≤ (2 : Q'))
      (coefficientError_succ_le_gaussian hq0 hq1 N r hr)) (Lcoef_abs_le x hx1 hxm1 r)
  have he : ((2 : Q') * (errorAmplitude q N * q ^ (r * r)))
        * (Q'.ofNat (r + 1) * Q'.ofNat (r + 1))
      ≈ ((2 : Q') * errorAmplitude q N)
        * ((Q'.ofNat (r + 1) * Q'.ofNat (r + 1)) * q ^ (r * r)) := by ring_qeqv
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (shiftedGaussian_le hq0 hq1 r)
        (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (errorAmplitude_nonnegative (Q'.le_of_lt hq0) N)))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

/-- Explicit derivative-error constant; it depends on q, not x or N. -/
def derivativeScale (q : Q') : Q' :=
  ((2 : Q') * lossScale (q * q) * shiftedGaussianScale q) * HKConv.divPos 1 (1 + -q)

theorem derivativeScale_nonnegative {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) : (0 : Q') ≤ derivativeScale q :=
  Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (lossScale_nonnegative _))
      (shiftedGaussianScale_nonnegative hq0 hq1)) (HKConv.divPos_nonneg Q'.zero_le_one)

/-- Whole original derivative versus twice the bare dPartial, with a common
geometric rate and every dependence explicit. Includes x=-1 and x=1. -/
theorem fullProdDx_sub_two_dPartial_le {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x) (N : Nat) :
    Q'.abs (JTPFullProductDerivativeNormalization.fullProdDx q x N
      + -((2 : Q') * JTPIdentity.dPartial q x N)) ≤ derivativeScale q * amp q N := by
  have hs := dsum_abs_le_sum (coefficientError q N) q
    ((2 : Q') * errorAmplitude q N * shiftedGaussianScale q) x N
    (fun r hr => derivativeError_term_le hq0 hq1 hx1 hxm1 N r (by omega))
  have hK := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (errorAmplitude_nonnegative (Q'.le_of_lt hq0) N))
    (shiftedGaussianScale_nonnegative hq0 hq1)
  have he : ((2 : Q') * errorAmplitude q N * shiftedGaussianScale q) * HKConv.divPos 1 (1 + -q)
      ≈ derivativeScale q * amp q N := by
    unfold derivativeScale errorAmplitude
    ring_qeqv
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (fullProdDx_sub_two_dPartial_eq hq0 hq1 hxm1 N)))
    (Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (HKConvGen.geom_series_le_base hq0 hq1 N) hK)
      (Q'.le_of_eqv he)))

/-- Computed power tolerance for the derivative comparison. -/
def derivativeTolerance (q ε : Q') : Q' := HKConv.divPos ε (derivativeScale q + 1)

theorem derivativeTolerance_pos (q : Q') {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < derivativeTolerance q ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem derivativeTolerance_budget {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) {ε : Q'} (hε : (0 : Q') < ε) :
    derivativeScale q * derivativeTolerance q ε ≤ ε := by
  have hp : (0 : Q') < derivativeScale q + 1 := Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (derivativeScale_nonnegative hq0 hq1))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
        (Q'.le_of_lt (derivativeTolerance_pos q hε)))
      (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp))))

/-- The derivative comparison modulus as Type-level data. -/
def derivativeCutoff (q ε : Q') : Nat := HKConvGen.powBaseCutoff q (derivativeTolerance q ε)

theorem derivative_bound_le {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : derivativeCutoff q ε ≤ N) :
    derivativeScale q * amp q N ≤ ε := by
  have hp : amp q N ≤ derivativeTolerance q ε := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1)
      (show HKConvGen.powBaseCutoff q (derivativeTolerance q ε) ≤ 2 * N + 1 from by
        unfold derivativeCutoff at hN; omega))
    (HKConvGen.pow_base_le_cutoff hq0 hq1 (derivativeTolerance_pos q hε))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (derivativeScale_nonnegative hq0 hq1))
    (derivativeTolerance_budget hq0 hq1 hε)

theorem fullProdDx_sub_two_dPartial_close {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hx1 : x ≤ (1 : Q')) (hxm1 : (-(1 : Q')) ≤ x)
    {ε : Q'} (hε : (0 : Q') < ε) (N : Nat) (hN : derivativeCutoff q ε ≤ N) :
    Q'.abs (JTPFullProductDerivativeNormalization.fullProdDx q x N
      + -((2 : Q') * JTPIdentity.dPartial q x N)) ≤ ε :=
  Q'.le_trans' _ _ _ (fullProdDx_sub_two_dPartial_le hq0 hq1 hx1 hxm1 N)
    (derivative_bound_le hq0 hq1 hε N hN)

end YMGap.Continuum.FiniteJacobiDerivativeComparison

#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.shiftedGaussianScale
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.one_le_shiftedGaussianScale
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.shiftedGaussianScale_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.shiftedGaussian_le
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.Lcoef_abs_le
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.dsum_bare_eq_two_dPartial
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.fullProdDx_sub_two_dPartial_eq
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeError_term_le
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeScale
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeScale_nonnegative
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.fullProdDx_sub_two_dPartial_le
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeTolerance
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeTolerance_pos
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeTolerance_budget
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivativeCutoff
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.derivative_bound_le
#print axioms YMGap.Continuum.FiniteJacobiDerivativeComparison.fullProdDx_sub_two_dPartial_close
