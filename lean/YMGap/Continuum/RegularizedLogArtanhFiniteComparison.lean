/-
# The original finite regularized logarithm and the actual artanh window

At cutoff 2*M the odd terms of the signed finite logarithm are exactly the
first M artanh terms.  The remaining finite defect is the computed primitive
from RegularizedLogPolynomialProductDefect, evaluated at the NEGATIVE
direct-window argument.  Its weighted coefficient norm gives an explicit
(2*M/6)*(5/6)^(2*M-1) error.  No analytic logarithm addition law, limiting
identification, operator calculus or physical estimate is assumed here.
-/

import YMGap.Continuum.RegularizedLogPrimitiveNorm
import YMGap.Constructive.CRealLogOddness
import YMGap.Constructive.FinSumAlg

namespace YMGap.Constructive.Q'.eqv

private theorem trans {a b c : Q'} (h : a.eqv b) (k : b.eqv c) : a.eqv c :=
  Q'.eqv_trans _ _ _ h k

private theorem symm {a b : Q'} (h : a.eqv b) : b.eqv a := Q'.eqv_symm h

end YMGap.Constructive.Q'.eqv

namespace YMGap.Continuum.RegularizedLogArtanhFiniteComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyPositivePrimitive (polynomialPower coordinate)
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFiniteLogDerivative
open YMGap.Constructive.QPolyFinitePowerDifference
open YMGap.Constructive.QPolyCoefficientEvaluation
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Continuum.RegularizedLogPolynomialProductDefect
open YMGap.Continuum.RegularizedLogPrimitiveNorm
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem mc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sc {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  q_add_congr h (Q'.neg_eqv_congr _ _ k)

private theorem constant_eval (c t : Q') : eval [c] t ≈ c :=
  (q_add_congr (Q'.eqv_refl c) (q_mul_zero t)).trans (q_add_zero_eqv c)

private theorem affine_eval (c d t : Q') : eval [c,d] t ≈ c+d*t :=
  (q_add_congr (Q'.eqv_refl c) (mc (Q'.eqv_refl t) (constant_eval d t))).trans
    (q_add_congr (Q'.eqv_refl c) (Q'.mul_comm_eqv t d))

private theorem coordinate_eval (t : Q') : eval coordinate t ≈ t :=
  (affine_eval 0 1 t).trans ((q_zero_add_eqv _).trans (Q'.one_mul_eqv t))

private def ell (t : Q') : Nat → Q'
  | 0 => 0
  | N+1 => ell t N+Q'.invSucc N*t^(N+1)

private theorem ell_congr {t u : Q'} (h : t ≈ u) : ∀ N, ell t N ≈ ell u N
  | 0 => Q'.eqv_refl 0
  | N+1 => q_add_congr (ell_congr h N)
      (mc (Q'.eqv_refl _) (BernsteinSequenceWrap.pow_eqv_congr h _))

private theorem finiteLog_ell (p : Poly) (t : Q') : ∀ N,
    eval (finiteLog p N) t ≈ ell (eval p t) N
  | 0 => Q'.eqv_refl 0
  | N+1 => (eval_padd _ _ t).trans
      (q_add_congr (finiteLog_ell p t N)
        ((eval_pscale _ _ t).trans
          (mc (Q'.eqv_refl _) (polynomialPower_eval p (N+1) t))))

private theorem partial_ell (x : Q') : ∀ N,
    RegularizedLogPolynomial.partialSum x N ≈ x*ell (1-x) N
  | 0 => (q_mul_zero x).symm
  | N+1 => (q_add_congr (partial_ell x N) (Q'.eqv_refl _)).trans
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 0) (.var 3))))
        (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => x | 1 => ell (1-x) N | 2 => Q'.invSucc N | _ => (1-x)^(N+1)))

private theorem ell_reflection (y : Q') : ∀ M,
    ell y (2*M)-ell (-y) (2*M) ≈
      CRealLog.partialSum y M+CRealLog.partialSum y M
  | 0 => by change (0 : Q')-0 ≈ 0+0; decide
  | M+1 => by
      have hidx : 2*(M+1) = (2*M+1)+1 := by omega
      have hodd := (CRealLogOddness.negPow_even_odd_eqv y M).2
      have heven : (-y)^((2*M+1)+1) ≈ y^((2*M+1)+1) := by
        simpa only [hidx] using (CRealLogOddness.negPow_even_odd_eqv y (M+1)).1
      rw [hidx]
      change ((ell y (2*M)+Q'.invSucc (2*M)*y^(2*M+1))+
          Q'.invSucc (2*M+1)*y^((2*M+1)+1))-
        ((ell (-y) (2*M)+Q'.invSucc (2*M)*(-y)^(2*M+1))+
          Q'.invSucc (2*M+1)*(-y)^((2*M+1)+1)) ≈ _
      have hreplace := sc (Q'.eqv_refl
          ((ell y (2*M)+Q'.invSucc (2*M)*y^(2*M+1))+
            Q'.invSucc (2*M+1)*y^((2*M+1)+1)))
        (q_add_congr (q_add_congr (Q'.eqv_refl (ell (-y) (2*M)))
          (mc (Q'.eqv_refl (Q'.invSucc (2*M))) hodd))
          (mc (Q'.eqv_refl (Q'.invSucc (2*M+1))) heven))
      refine hreplace.trans ?_
      have hgroup :
          ((ell y (2*M)+Q'.invSucc (2*M)*y^(2*M+1))+
            Q'.invSucc (2*M+1)*y^((2*M+1)+1))-
          ((ell (-y) (2*M)+Q'.invSucc (2*M)*(-y^(2*M+1)))+
            Q'.invSucc (2*M+1)*y^((2*M+1)+1)) ≈
          (ell y (2*M)-ell (-y) (2*M))+
            (CRealLog.term y M+CRealLog.term y M) := by
        change _ ≈ (ell y (2*M)-ell (-y) (2*M))+
          (y^(2*M+1)*Q'.invSucc (2*M)+y^(2*M+1)*Q'.invSucc (2*M))
        exact poly_identity_of_normal_eq
          (.add (.add (.add (.var 0) (.mul (.var 2) (.var 3)))
              (.mul (.var 4) (.var 5)))
            (.neg (.add (.add (.var 1) (.mul (.var 2) (.neg (.var 3))))
              (.mul (.var 4) (.var 5)))))
          (.add (.add (.var 0) (.neg (.var 1)))
            (.add (.mul (.var 3) (.var 2)) (.mul (.var 3) (.var 2))))
          (by decide) (fun | 0 => ell y (2*M) | 1 => ell (-y) (2*M) | 2 => Q'.invSucc (2*M) | 3 => y^(2*M+1) | 4 => Q'.invSucc (2*M+1) | _ => y^((2*M+1)+1))
      exact hgroup.trans ((q_add_congr (ell_reflection y M) (Q'.eqv_refl _)).trans
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1)))
          (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
          (by decide) (fun | 0 => CRealLog.partialSum y M | _ => CRealLog.term y M)))

/-- Exact finite odd/even cancellation; no interval or infinite-series premise. -/
theorem finiteLog_artanh_reflection (y : Q') (M : Nat) :
    eval (finiteLog coordinate (2*M)) y-eval (finiteLog coordinate (2*M)) (-y) ≈
      CRealLog.partialSum y M+CRealLog.partialSum y M :=
  (sc ((finiteLog_ell coordinate y _).trans (ell_congr (coordinate_eval y) _))
    ((finiteLog_ell coordinate (-y) _).trans (ell_congr (coordinate_eval (-y)) _))).trans
      (ell_reflection y M)

private theorem affine_yOf (x : Q') (hm1 : (0 : Q') < x+1) :
    1-x+x*CRealLog.yOf x hm1 ≈ -(CRealLog.yOf x hm1) := by
  let v := Q'.recipPos (x+1) hm1
  have hi : (x+1)*v ≈ 1 := Q'.mul_recipPos_eqv (x+1) hm1
  have hring : 1-x+x*((x-1)*v) ≈
      (x-1)*((x+1)*v-1)-((x-1)*v) :=
    poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 0) (.mul (.add (.var 0) (.neg (.const 1))) (.var 1))))
      (.add (.mul (.add (.var 0) (.neg (.const 1)))
          (.add (.mul (.add (.var 0) (.const 1)) (.var 1)) (.neg (.const 1))))
        (.neg (.mul (.add (.var 0) (.neg (.const 1))) (.var 1))))
      (by decide) (fun | 0 => x | _ => v)
  exact hring.trans ((sc (mc (Q'.eqv_refl _) (sc hi (Q'.eqv_refl 1)))
    (Q'.eqv_refl _)).trans
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.const 1) (.neg (.const 1)))) (.neg (.var 1)))
        (.neg (.var 1)) (by decide) (fun | 0 => x-1 | _ => (x-1)*v)))

/-- The signed comparison is EXACTLY the original defect polynomial, evaluated
at the actual direct-window artanh coordinate. No positivity is required. -/
theorem partial_logRat_defect (x : Q') (hm1 : (0 : Q') < x+1)
    (hyb : Q'.abs (CRealLog.yOf x hm1) ≤ CRealLog.recipOdd 1) (M : Nat) :
    RegularizedLogPolynomial.partialSum x (2*M)+x*((CRealLog.logRat x hm1 hyb).approx M) ≈
      x*eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1) := by
  let y := CRealLog.yOf x hm1
  have ha : eval [1-x,x] y ≈ -y :=
    (affine_eval _ _ _).trans (affine_yOf x hm1)
  have hd : eval (defectPolynomial x (2*M)) y ≈
      ell (1-x) (2*M)+(CRealLog.partialSum y M+CRealLog.partialSum y M) :=
    (eval_padd _ _ y).trans
      ((q_add_congr
        ((finiteLog_ell [1-x] y _).trans (ell_congr (constant_eval (1-x) y) _))
        ((eval_psub _ _ y).trans
          ((sc ((finiteLog_ell coordinate y _).trans (ell_congr (coordinate_eval y) _))
            ((finiteLog_ell [1-x,x] y _).trans (ell_congr ha _))).trans
              (ell_reflection y M)))))
  rw [CRealLog.logRat_approx]
  exact (q_add_congr (partial_ell x _) (Q'.eqv_refl _)).trans
    ((Q'.mul_add_eqv _ _ _).symm.trans (mc (Q'.eqv_refl x) hd.symm))

private theorem affine_norm (rho r x : Q') (hr : (0 : Q') ≤ r) (hx : (0 : Q') ≤ x) :
    weightedL1 rho [r,x] ≈ r+rho*x := by
  change Q'.abs r+rho*(Q'.abs x+rho*0) ≈ r+rho*x
  rw [ExpNeg.abs_of_nonneg hr, ExpNeg.abs_of_nonneg hx]
  exact q_add_congr (Q'.eqv_refl r)
    (mc (Q'.eqv_refl rho) ((q_add_congr (Q'.eqv_refl x) (q_mul_zero rho)).trans (q_add_zero_eqv x)))

private theorem complement_half (x : Q') (hhalf : HalfPow.half ≤ x) :
    1-x ≤ HalfPow.half :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hhalf))
    (by decide : (1 : Q')-HalfPow.half ≤ HalfPow.half)

/-- Explicit comparison of the actual finite regularized polynomial and the
actual rational artanh approximation. M is positive only to write 2*M-1. -/
theorem partial_logRat_error (x : Q') (hx0 : (0 : Q') ≤ x) (hx1 : x ≤ 1)
    (hhalf : HalfPow.half ≤ x) (hm1 : (0 : Q') < x+1)
    (hyb : Q'.abs (CRealLog.yOf x hm1) ≤ CRealLog.recipOdd 1)
    (M : Nat) (hM : 0 < M) :
    Q'.abs (RegularizedLogPolynomial.partialSum x (2*M)+
      x*((CRealLog.logRat x hm1 hyb).approx M)) ≤
      (Q'.mkPos 5 6 (by decide))^(2*M-1)*
        (Q'.mkPos 1 6 (by decide)*Q'.ofNat (2*M)) := by
  let rho := CRealLog.recipOdd 1
  let R := Q'.mkPos 5 6 (by decide)
  let row := powerDifferenceRow [1-x,x] coordinate (2*M)
  let G := pscale (1-x) row
  have hrho : (0 : Q') ≤ rho := by decide
  have hR : (0 : Q') ≤ R := by decide
  have hr : (0 : Q') ≤ 1-x := Q'.sub_nonneg_of_le hx1
  have hrhalf : 1-x ≤ HalfPow.half := complement_half x hhalf
  have hp : weightedL1 rho [1-x,x] ≤ R :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (affine_norm rho (1-x) x hr hx0))
      (Q'.le_trans' _ _ _ (Q'.add_le_add hrhalf
        (Q'.mul_le_mul_of_nonneg_left _ _ rho hx1 hrho))
        (by decide : HalfPow.half+rho*1 ≤ R))
  have hq : weightedL1 rho coordinate ≤ R := by decide
  have hidx : (2*M-1)+1 = 2*M := by omega
  have hrow : weightedL1 rho row ≤ Q'.ofNat (2*M)*R^(2*M-1) := by
    have h := powerDifferenceRow_weightedL1_le rho hrho [1-x,x] coordinate R hR hp hq (2*M-1)
    simpa only [hidx] using h
  have hG : weightedL1 rho G ≤ (1-x)*(Q'.ofNat (2*M)*R^(2*M-1)) := by
    have h := weightedL1_pscale_le rho hrho (1-x) row
    rw [ExpNeg.abs_of_nonneg hr] at h
    exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_left _ _ (1-x) hrow hr)
  have hprimitive : weightedL1 rho (primitive G) ≤
      rho*((1-x)*(Q'.ofNat (2*M)*R^(2*M-1))) :=
    Q'.le_trans' _ _ _ (primitive_weightedL1_le rho hrho G)
      (Q'.mul_le_mul_of_nonneg_left _ _ rho hG hrho)
  have hpin : eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1) ≈
      eval (primitive G) (CRealLog.yOf x hm1) :=
    (coefficient_eval (defect_primitive x (2*M)) _).symm
  have hdefect : Q'.abs (eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1)) ≤
      rho*((1-x)*(Q'.ofNat (2*M)*R^(2*M-1))) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (abs_eval_le_weightedL1 hrho hyb (primitive G)) hprimitive)
  have hfactor : Q'.abs (x*eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1)) ≤
      Q'.abs (eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1)) := by
    have h := ExpNeg.abs_mul_le x (eval (defectPolynomial x (2*M)) (CRealLog.yOf x hm1))
    rw [ExpNeg.abs_of_nonneg hx0] at h
    exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hx1 (Q'.abs_nonneg _))
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  have hcount : (0 : Q') ≤ Q'.ofNat (2*M) := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg (2*M)
  have hsmall : rho*((1-x)*(Q'.ofNat (2*M)*R^(2*M-1))) ≤
      rho*(HalfPow.half*(Q'.ofNat (2*M)*R^(2*M-1))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ rho
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrhalf
        (Q'.mul_nonneg _ _ hcount (Q'.pow_nonneg R hR _))) hrho
  have hend : rho*(HalfPow.half*(Q'.ofNat (2*M)*R^(2*M-1))) ≈
      R^(2*M-1)*(Q'.mkPos 1 6 (by decide)*Q'.ofNat (2*M)) := by
    have hconstant : rho*HalfPow.half ≈ Q'.mkPos 1 6 (by decide) := by decide
    exact (Q'.mul_assoc_eqv _ _ _).symm.trans
      ((mc hconstant (Q'.eqv_refl _)).trans
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 2) (.mul (.var 0) (.var 1))) (by decide)
          (fun | 0 => Q'.mkPos 1 6 (by decide) | 1 => Q'.ofNat (2*M) | _ => R^(2*M-1))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (partial_logRat_defect x hm1 hyb M)))
    (Q'.le_trans' _ _ _ hfactor
      (Q'.le_trans' _ _ _ hdefect (Q'.le_trans' _ _ _ hsmall (Q'.le_of_eqv hend))))

end YMGap.Continuum.RegularizedLogArtanhFiniteComparison

#print axioms YMGap.Continuum.RegularizedLogArtanhFiniteComparison.finiteLog_artanh_reflection
#print axioms YMGap.Continuum.RegularizedLogArtanhFiniteComparison.partial_logRat_defect
#print axioms YMGap.Continuum.RegularizedLogArtanhFiniteComparison.partial_logRat_error
