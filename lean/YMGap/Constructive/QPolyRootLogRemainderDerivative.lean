/-
Exact derivative of the ORIGINAL finite F, computed from the actual S.
F=D^(M+1)/(M+1)-u^N*S and F'=N*u^(N-1)*(S+h^(N*M)).
All equalities are at padded coefficients, including u=0, N=1 and M=0.
No sign, inverse root, integration, or operator identification is assumed.
-/

import YMGap.Constructive.QPolyRootLogInitial

namespace YMGap.Constructive.QPolyRootLogRemainderDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyRootLogDifference
open YMGap.Constructive.QPolyRootLogInitial

private theorem sub_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (psub p q) (psub p' q') := CoeffEqv.padd hp hq.pneg

private theorem pderiv_sub (p q : Poly) :
    CoeffEqv (pderiv (psub p q)) (psub (pderiv p) (pderiv q)) :=
  (pderiv_padd p (pneg q)).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (pderiv_pscale (-1) q))

private theorem mul_sub_right (p q r : Poly) :
    CoeffEqv (pmul p (psub q r)) (psub (pmul p q) (pmul p r)) :=
  (coeffEqv_pmul_padd_right p q (pneg r)).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pmul_pscale (-1) p r))

private theorem scale_neg (k : Q') (p : Poly) :
    CoeffEqv (pscale k (pneg p)) (pneg (pscale k p)) :=
  (coeffEqv_pscale_comp k (-1) p).trans
    ((coeffEqv_pscale_scalar (Q'.mul_comm_eqv k (-1)) p).trans
      (coeffEqv_pscale_comp (-1) k p).symm)

private theorem scale_sub (k : Q') (p q : Poly) :
    CoeffEqv (pscale k (psub p q)) (psub (pscale k p) (pscale k q)) :=
  (coeffEqv_pscale_padd k p (pneg q)).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (scale_neg k q))

private theorem subtract_negative_sum (p q r : Poly) :
    CoeffEqv (psub p (padd (pneg q) r)) (psub (padd p q) r) :=
  (CoeffEqv.padd (CoeffEqv.refl p)
    ((coeffEqv_pneg_padd (pneg q) r).trans
      (CoeffEqv.padd (coeffEqv_pneg_pneg q) (CoeffEqv.refl _)))).trans
    (coeffEqv_padd_assoc p q (pneg r)).symm

private theorem subtract_sum_difference (p q r : Poly) :
    CoeffEqv (psub (padd p q) (psub p r)) (padd q r) := by
  have hc : CoeffEqv (padd (padd p (pneg p)) (padd q r))
      (padd [] (padd q r)) :=
    CoeffEqv.padd (coeffEqv_padd_pneg_self p) (CoeffEqv.refl (padd q r))
  exact (CoeffEqv.padd (CoeffEqv.refl _)
    ((coeffEqv_pneg_padd p (pneg r)).trans
      (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pneg_pneg r)))).trans
    ((coeffEqv_padd_interchange p q (pneg p) r).trans hc)

private theorem root_power_derivative (n : Nat) :
    CoeffEqv (pderiv (rootPower n))
      (pneg (pscale (Q'.ofNat (n + 1)) (polynomialPower complement n))) := by
  have hd : CoeffEqv (pderiv complement) (pneg [1]) := by
    intro i
    cases i with
    | zero =>
        exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (-1))
          (Q'.eqv_symm (Q'.mul_one_eqv (-1)))
    | succ i => exact Q'.eqv_refl 0
  exact (power_derivative_succ complement n).trans
    ((((hd.pmul (CoeffEqv.refl _)).trans
      ((coeffEqv_pscale_pmul (-1) [1] _).trans
        ((coeffEqv_pmul_one_left _).pneg))).pscale _).trans
      (scale_neg _ _))

private theorem defect_antiderivative (n m : Nat) :
    CoeffEqv
      (pderiv (pscale (Q'.invSucc m) (polynomialPower (rootDefect n) (m + 1))))
      (pscale (Q'.ofNat (n + 1))
        (pmul (polynomialPower complement n) (polynomialPower (rootDefect n) m))) := by
  have hinv : (Q'.invSucc m * Q'.ofNat (m + 1)).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc m)
  exact (pderiv_pscale _ _).trans
    (((power_derivative_succ (rootDefect n) m).pscale _).trans
      ((coeffEqv_pscale_comp _ _ _).trans
        ((coeffEqv_pscale_scalar hinv _).trans
          ((coeffEqv_pscale_one _).trans
            (((rootDefect_derivative n).pmul (CoeffEqv.refl _)).trans
              (coeffEqv_pscale_pmul _ _ _))))))

/-- EXACT original F' identity, with no premise supplying its sign. -/
theorem rootLogRemainder_derivative (n m : Nat) :
    CoeffEqv (pderiv (rootLogRemainder n m))
      (pscale (Q'.ofNat (n + 1))
        (pmul (polynomialPower complement n)
          (padd (rootLogDifference n m) (polynomialPower coordinate ((n + 1) * m))))) := by
  let N := Q'.ofNat (n + 1)
  let U := polynomialPower complement n
  let S := rootLogDifference n m
  let D := polynomialPower (rootDefect n) m
  let H := polynomialPower coordinate ((n + 1) * m)
  have hleft : CoeffEqv (pmul (pderiv (rootPower n)) S)
      (pneg (pscale N (pmul U S))) :=
    ((root_power_derivative n).pmul (CoeffEqv.refl S)).trans
      ((coeffEqv_pscale_pmul (-1) (pscale N U) S).trans
        ((coeffEqv_pscale_pmul N U S).pneg))
  have hright : CoeffEqv (pmul (rootPower n) (pderiv S))
      (pscale N (pmul U (psub D H))) :=
    ((coeffEqv_pmul_comm complement U).pmul (CoeffEqv.refl _)).trans
      ((coeffEqv_pmul_assoc U complement (pderiv S)).trans
        (((CoeffEqv.refl U).pmul (rootLogDifference_cleared_derivative n m)).trans
          (coeffEqv_pmul_pscale N U (psub D H))))
  have hprod : CoeffEqv (pderiv (pmul (rootPower n) S))
      (padd (pneg (pscale N (pmul U S))) (pscale N (pmul U (psub D H)))) :=
    (pderiv_pmul (rootPower n) S).trans (CoeffEqv.padd hleft hright)
  have hsum : CoeffEqv
      (padd (pscale N (pmul U D)) (pscale N (pmul U S)))
      (pscale N (pmul U (padd D S))) :=
    (coeffEqv_pscale_padd N (pmul U D) (pmul U S)).symm.trans
      ((coeffEqv_pmul_padd_right U D S).symm.pscale N)
  exact (pderiv_sub _ _).trans
    ((sub_congr (defect_antiderivative n m) hprod).trans
      ((subtract_negative_sum _ _ _).trans
        ((sub_congr hsum (CoeffEqv.refl _)).trans
          ((scale_sub N _ _).symm.trans
            (((mul_sub_right U (padd D S) (psub D H)).symm.trans
              ((CoeffEqv.refl U).pmul (subtract_sum_difference D S H))).pscale N)))))

#print axioms rootLogRemainder_derivative

end YMGap.Constructive.QPolyRootLogRemainderDerivative
