/-
# The complementary-power telescope at actual polynomial coefficients

For u=1-h this proves 1-u^(n+1)-h^(n+1)=u*h*sum_(k<n)(u^k+h^k),
including the empty sum. The original root defect is also identified with
h times its actual finite geometric sum. No scalar-only identity, division,
positivity oracle, or operator calculus is used.
-/

import YMGap.Constructive.QPolyRootLogDifference

namespace YMGap.Constructive.QPolyComplementaryTelescope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Constructive.QPolyPositivePrimitive
open YMGap.Constructive.QPolyFiniteGeometric
open YMGap.Constructive.QPolyRootLogDifference (rootDefect)

/-- Actual coefficient row of the two finite geometric sums. -/
def complementaryPowerPolynomial (n : Nat) : Poly :=
  padd (geometricPolynomial complement n) (geometricPolynomial coordinate n)

private theorem complement_coordinate : CoeffEqv (psub [1] complement) coordinate := by
  intro i
  cases i with
  | zero => exact (by decide)
  | succ i =>
      cases i with
      | zero => exact (by decide)
      | succ i => exact Q'.eqv_refl 0

private theorem coordinate_complement : CoeffEqv (psub [1] coordinate) complement := by
  intro i
  cases i with
  | zero => exact (by decide)
  | succ i =>
      cases i with
      | zero => exact (by decide)
      | succ i => exact Q'.eqv_refl 0

private theorem sub_congr {p p' q q' : Poly}
    (hp : CoeffEqv p p') (hq : CoeffEqv q q') :
    CoeffEqv (psub p q) (psub p' q') := CoeffEqv.padd hp hq.pneg

private theorem mul_sub (p q r : Poly) :
    CoeffEqv (pmul p (psub q r)) (psub (pmul p q) (pmul p r)) :=
  (coeffEqv_pmul_padd_right p q (pneg r)).trans
    (CoeffEqv.padd (CoeffEqv.refl _) (coeffEqv_pmul_pscale (-1) p r))

private theorem sub_add_shuffle (p q r : Poly) :
    CoeffEqv (psub (padd p q) r) (padd (psub p r) q) :=
  (coeffEqv_padd_assoc p q (pneg r)).trans
    ((CoeffEqv.padd (CoeffEqv.refl p) (coeffEqv_padd_comm q (pneg r))).trans
      (coeffEqv_padd_assoc p (pneg r) q).symm)

private theorem geometric_head (p : Poly) (n : Nat) :
    CoeffEqv (geometricPolynomial p (n+1))
      (padd [1] (pmul p (geometricPolynomial p n))) := by
  induction n with
  | zero =>
      exact (CoeffEqv.padd (CoeffEqv.refl [1]) (coeffEqv_pmul_comm p [])).symm
  | succ n ih =>
      exact (CoeffEqv.padd ih (CoeffEqv.refl (pmul p (polynomialPower p n)))).trans
        ((coeffEqv_padd_assoc [1] (pmul p (geometricPolynomial p n))
          (pmul p (polynomialPower p n))).trans
          (CoeffEqv.padd (CoeffEqv.refl [1])
            (coeffEqv_pmul_padd_right p (geometricPolynomial p n)
              (polynomialPower p n)).symm))

/-- The ORIGINAL root defect has the computed positive-factor shape h*G(u).
This statement is coefficientwise and has no interval or spectral premise. -/
theorem root_defect_positive_factor (n : Nat) :
    CoeffEqv (rootDefect n)
      (pmul coordinate (geometricPolynomial complement (n+1))) :=
  (geometric_telescope complement (n+1)).symm.trans
    (complement_coordinate.pmul (CoeffEqv.refl _))

/-- Exact complementary-power factorization at all padded coefficients,
including n=0. It supplies the polynomial u factor needed before cancelling
the original S' identity; it does not cancel an operator with a kernel. -/
theorem complementary_power_defect (n : Nat) :
    CoeffEqv
      (psub (psub [1] (polynomialPower complement (n+1)))
        (polynomialPower coordinate (n+1)))
      (pmul (pmul complement coordinate) (complementaryPowerPolynomial n)) := by
  let U := geometricPolynomial complement n
  let H := geometricPolynomial coordinate n
  let hN := polynomialPower coordinate n
  have hf : CoeffEqv
      (psub (psub [1] (polynomialPower complement (n+1)))
        (polynomialPower coordinate (n+1)))
      (pmul coordinate (psub (geometricPolynomial complement (n+1)) hN)) :=
    (sub_congr (root_defect_positive_factor n) (CoeffEqv.refl _)).trans
      (mul_sub coordinate (geometricPolynomial complement (n+1)) hN).symm
  have hi : CoeffEqv (psub (geometricPolynomial complement (n+1)) hN)
      (pmul complement (padd H U)) :=
    (sub_congr (geometric_head complement n) (CoeffEqv.refl hN)).trans
      ((sub_add_shuffle [1] (pmul complement U) hN).trans
        ((CoeffEqv.padd
          ((geometric_telescope coordinate n).symm.trans
            (coordinate_complement.pmul (CoeffEqv.refl H)))
          (CoeffEqv.refl (pmul complement U))).trans
          (coeffEqv_pmul_padd_right complement H U).symm))
  exact hf.trans
    (((CoeffEqv.refl coordinate).pmul hi).trans
      ((coeffEqv_pmul_assoc coordinate complement (padd H U)).symm.trans
        (CoeffEqv.pmul (coeffEqv_pmul_comm coordinate complement)
          (coeffEqv_padd_comm H U))))

#print axioms complementaryPowerPolynomial
#print axioms root_defect_positive_factor
#print axioms complementary_power_defect

end YMGap.Constructive.QPolyComplementaryTelescope
