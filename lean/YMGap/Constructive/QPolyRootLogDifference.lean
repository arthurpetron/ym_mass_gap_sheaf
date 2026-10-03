/-
The ORIGINAL finite root/log difference, with coefficient-level derivative
identities.  The variable is h, u=1-h, N=n+1 and D=1-u^N.  The computed S is
N*sum_(k<N*M) h^(k+1)/(k+1) - sum_(k<M) D^(k+1)/(k+1).

No interval hypothesis, division by u, positive spectral floor or operator
identification is used.  Positivity and the SAME-root lift remain separate.
-/

import YMGap.Constructive.QPolyFiniteLogDerivative

namespace YMGap.Constructive.QPolyRootLogDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyFiniteLogDerivative

/-- The actual positive root power, with N=n+1. -/
def rootPower (n : Nat) : Poly := polynomialPower complement (n + 1)

/-- The actual defect D=1-u^N. -/
def rootDefect (n : Nat) : Poly := psub [1] (rootPower n)

/-- Actual finite S, not a replacement polynomial carrying an assumed sign. -/
def rootLogDifference (n m : Nat) : Poly :=
  psub (pscale (Q'.ofNat (n + 1)) (finiteLog coordinate ((n + 1) * m)))
    (finiteLog (rootDefect n) m)

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

private theorem sub_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (psub p q) (psub p' q') :=
  CoeffEqv.padd hp hq.pneg

private theorem double_complement (p : Poly) :
    CoeffEqv (psub [1] (psub [1] p)) p :=
  ((CoeffEqv.padd (CoeffEqv.refl [1])
      ((coeffEqv_pneg_padd [1] (pneg p)).trans
        (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pneg_pneg p)))).trans
    ((coeffEqv_padd_assoc [1] (pneg [1]) p).symm.trans
      (CoeffEqv.padd (coeffEqv_padd_pneg_self [1]) (CoeffEqv.refl p))))

private theorem subtract_complements (p q : Poly) :
    CoeffEqv (psub (psub [1] p) (psub [1] q)) (psub q p) :=
  (CoeffEqv.padd (CoeffEqv.refl _)
    ((coeffEqv_pneg_padd [1] (pneg q)).trans
      (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pneg_pneg q)))).trans
    ((coeffEqv_padd_interchange [1] (pneg p) (pneg [1]) q).trans
      ((CoeffEqv.padd (coeffEqv_padd_pneg_self [1])
        (CoeffEqv.refl _)).trans (coeffEqv_padd_comm (pneg p) q)))

private theorem coordinate_complement :
    CoeffEqv (psub [1] coordinate) complement := by
  intro i
  cases i with
  | zero => exact (by decide)
  | succ i =>
      cases i with
      | zero => exact (by decide)
      | succ i => exact Q'.eqv_refl 0

private theorem coordinate_derivative : CoeffEqv (pderiv coordinate) [1] := by
  intro i
  cases i with
  | zero => exact Q'.one_mul_eqv 1
  | succ i => exact Q'.eqv_refl 0

private theorem mul_constant (k : Q') (p : Poly) :
    CoeffEqv (pmul [k] p) (pscale k p) := by
  intro i
  change (coeff (padd (pscale k p) [0]) i).eqv (coeff (pscale k p) i)
  have hz : (coeff [0] i).eqv 0 := by
    cases i <;> exact Q'.eqv_refl 0
  exact Q'.eqv_trans _ _ _ (coeff_padd i _ _)
    (Q'.eqv_trans _ _ _ (q_add_congr (Q'.eqv_refl _) hz)
      (q_add_zero_eqv _))

private theorem complement_power_derivative (n : Nat) :
    CoeffEqv (pderiv (rootPower n))
      (pscale (-Q'.ofNat (n + 1)) (polynomialPower complement n)) := by
  have hd : CoeffEqv (pderiv complement) [-1] := by
    intro i
    cases i with
    | zero => exact Q'.one_mul_eqv (-1)
    | succ i => exact Q'.eqv_refl 0
  have hs : (Q'.ofNat (n + 1) * (-1)).eqv (-Q'.ofNat (n + 1)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv _ 1)
      (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv _))
  exact (power_derivative_succ complement n).trans
    ((((hd.pmul (CoeffEqv.refl _)).trans (mul_constant (-1) _)).pscale _).trans
      ((coeffEqv_pscale_comp _ _ _).trans
        (coeffEqv_pscale_scalar hs _)))

/-- D'=N*u^(N-1), at every padded coefficient. -/
theorem rootDefect_derivative (n : Nat) :
    CoeffEqv (pderiv (rootDefect n))
      (pscale (Q'.ofNat (n + 1)) (polynomialPower complement n)) := by
  have hs : ((-1 : Q') * (-Q'.ofNat (n + 1))).eqv (Q'.ofNat (n + 1)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
      (Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)) (Q'.neg_neg_eqv _))
  exact (pderiv_sub [1] (rootPower n)).trans
    ((complement_power_derivative n).pneg.trans
      ((coeffEqv_pscale_comp (-1) _ _).trans
        (coeffEqv_pscale_scalar hs _)))

/-- The actual S' before clearing u. -/
theorem rootLogDifference_derivative (n m : Nat) :
    CoeffEqv (pderiv (rootLogDifference n m))
      (psub
        (pscale (Q'.ofNat (n + 1)) (geometricPolynomial coordinate ((n + 1) * m)))
        (pscale (Q'.ofNat (n + 1))
          (pmul (polynomialPower complement n) (geometricPolynomial (rootDefect n) m)))) := by
  have hh : CoeffEqv (pderiv (finiteLog coordinate ((n + 1) * m)))
      (geometricPolynomial coordinate ((n + 1) * m)) :=
    (finiteLog_derivative coordinate _).trans
      ((coordinate_derivative.pmul (CoeffEqv.refl _)).trans
        (coeffEqv_pmul_one_left _))
  have hD : CoeffEqv (pderiv (finiteLog (rootDefect n) m))
      (pscale (Q'.ofNat (n + 1))
        (pmul (polynomialPower complement n) (geometricPolynomial (rootDefect n) m))) :=
    (finiteLog_derivative (rootDefect n) m).trans
      (((rootDefect_derivative n).pmul (CoeffEqv.refl _)).trans
        (coeffEqv_pscale_pmul _ _ _))
  exact (pderiv_sub _ _).trans
    (sub_congr ((pderiv_pscale _ _).trans (hh.pscale _)) hD)

/-- EXACT original identity u*S'=N*(D^M-h^(N*M)), including N=1 and M=0.
This does not cancel or divide by u, and does not assert positivity. -/
theorem rootLogDifference_cleared_derivative (n m : Nat) :
    CoeffEqv (pmul complement (pderiv (rootLogDifference n m)))
      (pscale (Q'.ofNat (n + 1))
        (psub (polynomialPower (rootDefect n) m)
          (polynomialPower coordinate ((n + 1) * m)))) := by
  let H := geometricPolynomial coordinate ((n + 1) * m)
  let G := geometricPolynomial (rootDefect n) m
  let U := polynomialPower complement n
  have hh : CoeffEqv (pmul complement H)
      (psub [1] (polynomialPower coordinate ((n + 1) * m))) :=
    ((coordinate_complement.symm.pmul (CoeffEqv.refl H)).trans
      (geometric_telescope coordinate _))
  have hD : CoeffEqv (pmul complement (pmul U G))
      (psub [1] (polynomialPower (rootDefect n) m)) :=
    (coeffEqv_pmul_assoc complement U G).symm.trans
      (((double_complement (rootPower n)).symm.pmul (CoeffEqv.refl G)).trans
        (geometric_telescope (rootDefect n) m))
  exact ((CoeffEqv.refl complement).pmul (rootLogDifference_derivative n m)).trans
    ((mul_sub_right _ _ _).trans
      ((sub_congr (coeffEqv_pmul_pscale _ _ _) (coeffEqv_pmul_pscale _ _ _)).trans
        ((scale_sub _ _ _).symm.trans
          (((sub_congr hh hD).pscale _).trans
            ((subtract_complements _ _).pscale _)))))

#print axioms rootPower
#print axioms rootDefect
#print axioms rootLogDifference
#print axioms rootDefect_derivative
#print axioms rootLogDifference_derivative
#print axioms rootLogDifference_cleared_derivative

end YMGap.Constructive.QPolyRootLogDifference
