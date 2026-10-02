/-
# Original Jacobi theta height under nome squaring

Pairing the original Gaussian-series terms proves Theta_q(1) <=
2*Theta_(q*q)(1) for EVERY rational 0<q<1. The first pair is paid
by half of the central term and a rational square inequality; all
later pairs are bounded by their original Gaussian exponents.

The finite comparison uses the literal bareTheta prefixes at 2*N
and N. The completed comparison uses the existing undifferentiated
Jacobi identity and the sound eventual order, not the one-slack order.
No heat floor, near-one hypothesis, supplied height comparison, or
Haar shape certificate is used. The full heat-profile and interacting
variance estimates remain separate obligations.
-/

import YMGap.Continuum.JacobiTripleProductOnBox
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealComplete
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.Soundness

namespace YMGap.Continuum.SU2HeatJacobiHeightComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteJacobiSeriesComparison (bareTheta)
open YMGap.Continuum.JacobiTripleProductOnBox
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem T_at_one : ∀ n : Nat, Cheb.T n 1 ≈ 1 ∧ Cheb.T (n+1) 1 ≈ 1
  | 0 => ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩
  | n+1 => by
      have h := T_at_one n
      refine ⟨h.2, ?_⟩
      rw [Cheb.T_succ_succ]
      exact Q'.eqv_trans _ _ _
        (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ h.2)
          (Q'.neg_eqv_congr _ _ h.1))
        (by decide : ((2 : Q')*1)*1 + -1 ≈ (1 : Q'))

private def gaussianHeight (q : Q') : Nat → Q'
  | 0 => 1
  | n+1 => gaussianHeight q n + 2*q^((n+1)*(n+1))

private theorem bareTheta_height (q : Q') : ∀ n : Nat,
    bareTheta q 1 n ≈ gaussianHeight q n
  | 0 => Q'.eqv_refl _
  | n+1 => by
      change bareTheta q 1 n + (2 : Q')*q^((n+1)*(n+1))*Cheb.T (n+1) 1
        ≈ gaussianHeight q n + 2*q^((n+1)*(n+1))
      exact Cheb.add_eqv_congr _ _ _ _ (bareTheta_height q n)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (T_at_one n).2)
          (Q'.mul_one_eqv _))

private theorem first_pair {q : Q'} (hq0 : (0 : Q') ≤ q)
    (hq1 : q ≤ (1 : Q')) :
    q^1 + q^4 ≤ HalfPow.half + 2*((q*q)^1) := by
  have he : q*HalfPow.half+q*HalfPow.half ≈ q :=
    Q'.eqv_trans _ _ _
      (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _))
      (ExpNeg.two_halves q)
  have hq : q ≤ HalfPow.half+q*q :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.le_trans' _ _ _ (CRealAlg.amgm_two q HalfPow.half)
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_left (q*q) _ _ (by decide : HalfPow.half*HalfPow.half ≤ HalfPow.half))
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _))))
  have h4 : q^4 ≤ q*q := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone hq0 hq1 (by decide : 2 ≤ 4))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q _ _ (Q'.mul_one_eqv q)) (Q'.eqv_refl _)))
  have hl : q^1 + q^4 ≤ q+q^4 :=
    Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q))
  exact Q'.le_trans' _ _ _ hl (Q'.le_trans' _ _ _ (Q'.add_le_add hq h4)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.add (.var 1) (.var 0)) (.var 0))
        (.add (.var 1) (.mul (.const 2) (.var 0)))
        (by decide) (fun | 0 => q*q | _ => HalfPow.half))
      (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm (Q'.mul_one_eqv (q*q))))))))

private theorem later_pair {q : Q'} (hq0 : (0 : Q') ≤ q)
    (hq1 : q ≤ (1 : Q')) (n : Nat) (hn : 1 ≤ n) :
    q^((2*n+1)*(2*n+1)) + q^((2*n+2)*(2*n+2))
      ≤ 2*((q*q)^((n+1)*(n+1))) := by
  have hn2 : 1 ≤ n*n := Nat.mul_le_mul hn hn
  have he : 2*((n+1)*(n+1)) ≤ (2*n+1)*(2*n+1) := by
    simp only [show (2 : Nat)=1+1 from rfl, Nat.add_mul, Nat.mul_add,
      Nat.one_mul, Nat.mul_one]
    omega
  have he' : (2*n+1)*(2*n+1) ≤ (2*n+2)*(2*n+2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpin := GaussQBinomEulerQuotient.square_pow q ((n+1)*(n+1))
  have ha := Q'.le_trans' _ _ _ (HKConvGen.pow_base_antitone hq0 hq1 he)
    (Q'.ge_of_eqv hpin)
  have hb := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone hq0 hq1 (Nat.le_trans he he')) (Q'.ge_of_eqv hpin)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add ha hb)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
      (by decide) (fun _ => (q*q)^((n+1)*(n+1)))))

private theorem gaussianHeight_doubled {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) : ∀ n : Nat,
    gaussianHeight q (2*n) ≤ 2*gaussianHeight (q*q) n
  | 0 => by change (1 : Q') ≤ 2*1; decide
  | n+1 => by
      cases n with
      | zero =>
          change (1+2*q^(1*1))+2*q^(2*2) ≤ 2*(1+2*(q*q)^(1*1))
          have hp := Q'.mul_le_mul_of_nonneg_left _ _ 2 (first_pair hq0 hq1) (by decide)
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (poly_identity_of_normal_eq
              (.add (.add (.const 1) (.mul (.const 2) (.var 0))) (.mul (.const 2) (.var 1)))
              (.add (.const 1) (.mul (.const 2) (.add (.var 0) (.var 1))))
              (by decide) (fun | 0 => q^1 | _ => q^4)))
            (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ hp)
              (Q'.le_of_eqv (Q'.eqv_trans _ _ _
                (Q'.eqv_trans _ _ _
                  (Q'.add_eqv_congr_left 1 _ _ (Q'.mul_add_eqv 2 HalfPow.half (2*(q*q)^1)))
                  (Q'.eqv_symm (Q'.add_assoc_eqv 1 (2*HalfPow.half) (2*(2*(q*q)^1)))))
                (Q'.eqv_trans _ _ _
                  (Q'.add_eqv_congr_right _ _ _ (by decide : (1 : Q')+2*HalfPow.half ≈ 2))
                  (poly_identity_of_normal_eq
                    (.add (.const 2) (.mul (.const 2) (.mul (.const 2) (.var 0))))
                    (.mul (.const 2) (.add (.const 1) (.mul (.const 2) (.var 0))))
                    (by decide) (fun _ => (q*q)^1))))))
      | succ k =>
          have hidx : 2*((k+1)+1)=2*(k+1)+1+1 := by omega
          rw [hidx, gaussianHeight, gaussianHeight, gaussianHeight]
          have hp := Q'.mul_le_mul_of_nonneg_left _ _ 2
            (later_pair hq0 hq1 (k+1) (by omega)) (by decide)
          have hi := gaussianHeight_doubled hq0 hq1 (k+1)
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (poly_identity_of_normal_eq
              (.add (.add (.var 0) (.mul (.const 2) (.var 1))) (.mul (.const 2) (.var 2)))
              (.add (.var 0) (.mul (.const 2) (.add (.var 1) (.var 2))))
              (by decide) (fun
                | 0 => gaussianHeight q (2*(k+1))
                | 1 => q^((2*(k+1)+1)*(2*(k+1)+1))
                | _ => q^((2*(k+1)+2)*(2*(k+1)+2)))))
            (Q'.le_trans' _ _ _ (Q'.add_le_add hi hp)
              (Q'.le_of_eqv (poly_identity_of_normal_eq
                (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.mul (.const 2) (.var 1))))
                (.mul (.const 2) (.add (.var 0) (.mul (.const 2) (.var 1))))
                (by decide) (fun
                  | 0 => gaussianHeight (q*q) (k+1)
                  | _ => (q*q)^(((k+1)+1)*((k+1)+1))))))

/-- Literal original theta-series prefixes, including the central one.
The leading constant is independent of the nome; both strict endpoints
are excluded only when subsequently forming the CReal completions. -/
theorem bareTheta_doubled_height {q : Q'}
    (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) (n : Nat) :
    bareTheta q 1 (2*n) ≤ 2*bareTheta (q*q) 1 n :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (bareTheta_height q (2*n)))
    (Q'.le_trans' _ _ _ (gaussianHeight_doubled hq0 hq1 n)
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left 2 _ _ (bareTheta_height (q*q) n))))

private theorem leEv_of_equiv {A B : CReal} (h : CReal.Equiv A B) : CReal.leEv A B :=
  fun e he => by
    obtain ⟨N,hN⟩ := h e he
    exact ⟨N, fun n hn => (hN n hn).1⟩

private theorem leEv_scale_two {A B : CReal} (h : CReal.leEv A B) :
    CReal.leEv (CReal.mul (CReal.ofQ' 2) A) (CReal.mul (CReal.ofQ' 2) B) := by
  intro e he
  obtain ⟨N,hN⟩ := h (HalfPow.half*e) (ExpNeg.half_mul_pos e he)
  refine ⟨N, fun n hn => ?_⟩
  have hpin : 2*(HalfPow.half*e) ≈ e :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half e))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ e (by decide : (2 : Q')*HalfPow.half ≈ 1))
        (Q'.one_mul_eqv e))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 (hN n hn) (by decide))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv 2 (B.approx n) (HalfPow.half*e))
      (Q'.add_eqv_congr_left _ _ _ hpin)))

/-- The EXISTING original completed theta products satisfy the height
comparison in the sound eventual order, for ALL strict nomes. -/
theorem thetaProduct_squared_nome_height {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    CReal.leEv (ThetaConvGen.thetaConvCRealGen hq0 hq1 (by decide) (Q'.le_refl' 1))
      (CReal.mul (CReal.ofQ' 2)
        (ThetaConvGen.thetaConvCRealGen (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1)
          (by decide) (Q'.le_refl' 1))) := by
  let A := fullThetaSeries hq0 hq1 (Q'.le_refl' 1) (by decide)
  let B := fullThetaSeries (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1)
    (Q'.le_refl' 1) (by decide)
  have hAB : CReal.leEv A (CReal.mul (CReal.ofQ' 2) B) := by
    intro e he
    obtain ⟨N,hN⟩ := A.cauchy e he
    refine ⟨N, fun n hn => ?_⟩
    have hpair : A.approx (2*n) ≤ 2*B.approx n :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (fullThetaSeries_approx hq0 hq1 (Q'.le_refl' 1) (by decide) (2*n)))
        (Q'.le_trans' _ _ _ (bareTheta_doubled_height (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) n)
          (Q'.ge_of_eqv (Q'.mul_eqv_congr_left 2 _ _
            (fullThetaSeries_approx (HKPos.q_mul_pos hq0 hq0)
              (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1)
              (Q'.le_refl' 1) (by decide) n))))
    exact Q'.le_trans' _ _ _ (hN n (2*n) hn (by omega)).1
      (Q'.add_le_add_right _ _ e hpair)
  exact CReal.leEv_trans
    (leEv_of_equiv (thetaProduct_eq_fullThetaSeries hq0 hq1 (Q'.le_refl' 1) (by decide)))
    (CReal.leEv_trans hAB (leEv_scale_two (leEv_of_equiv
      (CReal.Equiv.symm (thetaProduct_eq_fullThetaSeries (HKPos.q_mul_pos hq0 hq0)
        (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1)
        (Q'.le_refl' 1) (by decide))))))

end YMGap.Continuum.SU2HeatJacobiHeightComparison

#print axioms YMGap.Continuum.SU2HeatJacobiHeightComparison.bareTheta_doubled_height
#print axioms YMGap.Continuum.SU2HeatJacobiHeightComparison.thetaProduct_squared_nome_height
