/-
Computed difference bounds for the actual rational polynomial syntax.
Only the generic cube/monomial bounds from the imported module are used;
no legacy action or transfer estimate is imported as a physical conclusion.
The constant is a finite coefficient-weighted total degree. It pays a
polynomial's raw-grid-to-sphere-repair error, not a continuum/mass-gap bound.
-/

import YMGap.Continuum.BF4CompactCoupledActionBounds
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.RatPolyCubeLipschitz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4CompactCoupledActionBounds

local infix:50 " ≈ " => Q'.eqv

/-- Syntactic total degree, including empty and zero-exponent monomials. -/
def monomialDegree : List Nat → Nat
  | [] => 0
  | exponent :: rest => exponent + monomialDegree rest

/-- An explicit rational cube Lipschitz constant, computed from the input. -/
def polynomialLipschitz : RatPoly → Q'
  | [] => 0
  | term :: rest => Q'.abs term.2 * Q'.ofNat (monomialDegree term.1) +
      polynomialLipschitz rest

theorem polynomialLipschitz_nonnegative :
    ∀ p : RatPoly, (0 : Q') ≤ polynomialLipschitz p
  | [] => Q'.le_refl' 0
  | term :: rest => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (Q'.abs_nonneg term.2)
        (ExpNeg.ofNat_nonneg' (monomialDegree term.1)))
      (polynomialLipschitz_nonnegative rest)

private theorem product_difference (a b c d : Q')
    (hc : Q'.abs c ≤ (1 : Q')) (hb : Q'.abs b ≤ (1 : Q')) :
    Q'.abs (a*c + -(b*d)) ≤ Q'.abs (a + -b) + Q'.abs (c + -d) := by
  have heq : a*c + -(b*d) ≈ (a + -b)*c + b*(c + -d) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
      (.add (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.mul (.var 1) (.add (.var 2) (.neg (.var 3)))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  have hleft : Q'.abs ((a + -b)*c) ≤ Q'.abs (a + -b) :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hc (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.mul_one_eqv _)))
  have hright : Q'.abs (b*(c + -d)) ≤ Q'.abs (c + -d) :=
    Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hb (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr heq))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add hleft hright))

private theorem power_abs_unit {x : Q'} (hx : Q'.abs x ≤ (1 : Q')) :
    ∀ n : Nat, Q'.abs (qpow x n) ≤ (1 : Q')
  | 0 => by change Q'.abs (1 : Q') ≤ 1; decide
  | n+1 => Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg (power_abs_unit hx n) hx
          Q'.zero_le_one (Q'.abs_nonneg _))
        (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem degree_mul_add (a b : Nat) (delta : Q') :
    Q'.ofNat a*delta + Q'.ofNat b*delta ≈ Q'.ofNat (a+b)*delta :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv a b)))

/-- Signed power sensitivity on [-1,1], including negative bases. -/
theorem power_difference {x y delta : Q'}
    (hx : Q'.abs x ≤ (1 : Q')) (hy : Q'.abs y ≤ (1 : Q'))
    (hd : Q'.abs (x + -y) ≤ delta) :
    ∀ n : Nat, Q'.abs (qpow x n + -(qpow y n)) ≤ Q'.ofNat n*delta
  | 0 => by
      have hzero : Q'.abs (qpow x 0 + -(qpow y 0)) ≈ (0 : Q') :=
        Q'.eqv_trans _ _ _ (ExpNeg.abs_eqv_congr (Q'.add_neg_self_eqv 1))
          (by decide : Q'.abs (0 : Q') ≈ 0)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero)
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) (Q'.zero_mul_eqv _)))
  | n+1 => by
      have hnat : Q'.ofNat n*delta + delta ≈ Q'.ofNat (n+1)*delta :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_symm (Q'.eqv_trans _ _ _
              (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.ofNat 1 ≈ (1 : Q')))
              (Q'.one_mul_eqv _))))
          (degree_mul_add n 1 delta)
      exact Q'.le_trans' _ _ _
        (product_difference (qpow x n) (qpow y n) x y hx (power_abs_unit hy n))
        (Q'.le_trans' _ _ _ (Q'.add_le_add (power_difference hx hy hd n) hd)
          (Q'.le_of_eqv hnat))

private theorem monomial_abs_unit (rho : Nat → Q')
    (hrho : CompactCubeEnvironment rho) :
    ∀ (start : Nat) (m : List Nat),
      Q'.abs (evalMonoFrom rho start m) ≤ (1 : Q')
  | _, [] => by change Q'.abs (1 : Q') ≤ 1; decide
  | start, exponent :: rest =>
      Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg (power_abs_unit (hrho start) exponent)
            (monomial_abs_unit rho hrho (start+1) rest)
            Q'.zero_le_one (Q'.abs_nonneg _))
          (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem monomial_difference_from (rho sigma : Nat → Q')
    (hrho : CompactCubeEnvironment rho) (hsigma : CompactCubeEnvironment sigma)
    (delta : Q') (hd : ∀ i, Q'.abs (rho i + -(sigma i)) ≤ delta) :
    ∀ (start : Nat) (m : List Nat),
      Q'.abs (evalMonoFrom rho start m + -(evalMonoFrom sigma start m)) ≤
        Q'.ofNat (monomialDegree m)*delta
  | _, [] => by
      change Q'.abs ((1 : Q') + -1) ≤ Q'.ofNat 0*delta
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (by decide : Q'.abs ((1 : Q') + -1) ≈ 0))
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv) (Q'.zero_mul_eqv _)))
  | start, exponent :: rest => by
      exact Q'.le_trans' _ _ _
        (product_difference (qpow (rho start) exponent) (qpow (sigma start) exponent)
          (evalMonoFrom rho (start+1) rest) (evalMonoFrom sigma (start+1) rest)
          (monomial_abs_unit rho hrho (start+1) rest)
          (power_abs_unit (hsigma start) exponent))
        (Q'.le_trans' _ _ _
          (Q'.add_le_add (power_difference (hrho start) (hsigma start) (hd start) exponent)
            (monomial_difference_from rho sigma hrho hsigma delta hd (start+1) rest))
          (Q'.le_of_eqv (degree_mul_add exponent (monomialDegree rest) delta)))

/-- Actual monomial variation, with its total degree as explicit constant. -/
theorem monomial_difference (rho sigma : Nat → Q')
    (hrho : CompactCubeEnvironment rho) (hsigma : CompactCubeEnvironment sigma)
    (delta : Q') (hd : ∀ i, Q'.abs (rho i + -(sigma i)) ≤ delta) (m : List Nat) :
    Q'.abs (evalMono rho m + -(evalMono sigma m)) ≤
      Q'.ofNat (monomialDegree m)*delta :=
  monomial_difference_from rho sigma hrho hsigma delta hd 0 m

/-- No supplied Lipschitz input: the original finite polynomial computes its
own signed cube-difference constant. This is not scaling-uniform in p. -/
theorem polynomial_difference (rho sigma : Nat → Q')
    (hrho : CompactCubeEnvironment rho) (hsigma : CompactCubeEnvironment sigma)
    (delta : Q') (hd : ∀ i, Q'.abs (rho i + -(sigma i)) ≤ delta) :
    ∀ p : RatPoly,
      Q'.abs (evalRatPoly rho p + -(evalRatPoly sigma p)) ≤ polynomialLipschitz p*delta
  | [] => by
      change Q'.abs ((0 : Q') + -0) ≤ 0*delta
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : Q'.abs ((0 : Q') + -0) ≈ 0))
        (Q'.ge_of_eqv (Q'.zero_mul_eqv _))
  | term :: rest => by
      have heq : evalRatPoly rho (term :: rest) + -(evalRatPoly sigma (term :: rest)) ≈
          term.2*(evalMono rho term.1 + -(evalMono sigma term.1)) +
          (evalRatPoly rho rest + -(evalRatPoly sigma rest)) :=
        poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.var 3))
            (.neg (.add (.mul (.var 0) (.var 2)) (.var 4))))
          (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
            (.add (.var 3) (.neg (.var 4))))
          (by decide) (fun
            | 0 => term.2
            | 1 => evalMono rho term.1
            | 2 => evalMono sigma term.1
            | 3 => evalRatPoly rho rest
            | _ => evalRatPoly sigma rest)
      have hterm : Q'.abs (term.2*(evalMono rho term.1 + -(evalMono sigma term.1))) ≤
          Q'.abs term.2*(Q'.ofNat (monomialDegree term.1)*delta) :=
        Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le _ _)
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (monomial_difference rho sigma hrho hsigma delta hd term.1) (Q'.abs_nonneg _))
      have hfactor : Q'.abs term.2*(Q'.ofNat (monomialDegree term.1)*delta) +
          polynomialLipschitz rest*delta ≈ polynomialLipschitz (term :: rest)*delta :=
        poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 3) (.var 2)))
            (.mul (.add (.mul (.var 0) (.var 1)) (.var 3)) (.var 2))
            (by decide) (fun
              | 0 => Q'.abs term.2
              | 1 => Q'.ofNat (monomialDegree term.1)
              | 2 => delta
              | _ => polynomialLipschitz rest)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr heq))
        (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
          (Q'.le_trans' _ _ _ (Q'.add_le_add hterm
            (polynomial_difference rho sigma hrho hsigma delta hd rest))
            (Q'.le_of_eqv hfactor)))

end YMGap.Continuum.RatPolyCubeLipschitz

#print axioms YMGap.Continuum.RatPolyCubeLipschitz.monomialDegree
#print axioms YMGap.Continuum.RatPolyCubeLipschitz.polynomialLipschitz
#print axioms YMGap.Continuum.RatPolyCubeLipschitz.polynomialLipschitz_nonnegative
#print axioms YMGap.Continuum.RatPolyCubeLipschitz.power_difference
#print axioms YMGap.Continuum.RatPolyCubeLipschitz.monomial_difference
#print axioms YMGap.Continuum.RatPolyCubeLipschitz.polynomial_difference
