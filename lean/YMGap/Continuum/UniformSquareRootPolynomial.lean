/-
# Explicit uniform polynomial square-root sequences

The division-free rational iteration has a uniform Cauchy rate on [0,1]:
for m>=n, (x_m-x_n)^2<=t-x_n^2, so the residual stage at epsilon^2
controls the unsquared difference. Polynomial coefficients are generated
by the same recurrence and their evaluation is proved equal to that
iteration. Both the polynomials and their squares carry actual uniform
Cauchy data; the squares converge uniformly to the coordinate polynomial.
The rational iteration also constructs a CReal square root with its own
QCauchy data and square identity, including at zero.

No operator square identity or geometric half-time identification is
assumed here. Fixed-spacing functional calculus and continuum/Clay
obligations remain distinct.
-/

import YMGap.Continuum.UniformSquareRootIteration
import YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear

namespace YMGap.Continuum.UniformSquareRootPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BernsteinSequenceWrap (eval01)
open YMGap.Continuum.BernsteinUniformConvergence (abs_of_nonneg)
open YMGap.Continuum.UniformSquareRootIteration
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction (UniformSequence)

theorem square_congr (a b : Q') (h : Q'.eqv a b) : Q'.eqv (a*a) (b*b) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ h)

theorem difference_square_le (a b : Q') (ha : (0 : Q')≤a) (hab : a≤b) :
    (b-a)*(b-a)≤b*b-a*a := by
  apply Q'.le_of_sub_nonneg
  have h := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q')≤2) ha)
    (Q'.sub_nonneg_of_le hab)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.var 0)) (.add (.var 1) (.neg (.var 0))))
    (.add (.add (.mul (.var 1) (.var 1)) (.neg (.mul (.var 0) (.var 0))))
      (.neg (.mul (.add (.var 1) (.neg (.var 0))) (.add (.var 1) (.neg (.var 0))))))
    (by decide) (fun | 0 => a | _ => b)))

def cauchyStage (epsilon : Q') : Nat := residualStage (epsilon*epsilon)

theorem iterate_tail_difference (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1)
    (epsilon : Q') (he : (0 : Q')<epsilon) (m n : Nat)
    (hm : cauchyStage epsilon≤m) (hmn : m≤n) : iterate t n≤iterate t m+epsilon := by
  have hab := iterate_mono t ht h1 hmn
  have hd := Q'.sub_nonneg_of_le hab
  have hs := difference_square_le (iterate t m) (iterate t n) (iterate_invariants t ht h1 m).1 hab
  have hb : (iterate t n-iterate t m)*(iterate t n-iterate t m)≤epsilon*epsilon :=
    Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ (iterate_invariants t ht h1 n).2.2)
      (residual_bound t ht h1 (epsilon*epsilon) (Q'.mul_pos he he) m hm))
  exact le_add_of_sub_le (le_of_sq_le_sq he hd hb)

theorem iterate_uniformCauchy (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : cauchyStage epsilon≤m) (hn : cauchyStage epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    iterate t m≤iterate t n+epsilon ∧ iterate t n≤iterate t m+epsilon := by
  rcases Nat.le_total m n with hmn | hnm
  · exact ⟨Q'.le_trans' _ _ _ (iterate_mono t ht h1 hmn)
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),iterate_tail_difference t ht h1 epsilon he m n hm hmn⟩
  · exact ⟨iterate_tail_difference t ht h1 epsilon he n m hn hnm,
      Q'.le_trans' _ _ _ (iterate_mono t ht h1 hnm) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

def iterateCauchy (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) : QCauchy (iterate t) where
  M := cauchyStage
  bound := fun epsilon he m n hm hn => iterate_uniformCauchy epsilon he m n hm hn t ht h1

def value (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) : CReal where
  approx := iterate t
  cauchy := fun epsilon he => ⟨cauchyStage epsilon,(iterateCauchy t ht h1).bound epsilon he⟩

def valueCauchy (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) : QCauchy (value t ht h1).approx :=
  iterateCauchy t ht h1

theorem value_square (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    Equiv (CReal.mul (value t ht h1) (value t ht h1)) (ofQ' t) := by
  intro epsilon he
  refine ⟨residualStage epsilon,fun n hn => ⟨?_,?_⟩⟩
  · exact Q'.le_trans' _ _ _ (iterate_invariants t ht h1 n).2.2
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))
  · exact le_add_of_sub_le (residual_bound t ht h1 epsilon he n hn)

def polynomialStep (p : QPoly.Poly) : QPoly.Poly :=
  QPoly.padd p (QPoly.pscale HalfPow.half (QPoly.psub [0,1] (QPoly.pmul p p)))

def polynomial : Nat → QPoly.Poly
  | 0 => []
  | n+1 => polynomialStep (polynomial n)

theorem step_congr (t x y : Q') (h : Q'.eqv x y) : Q'.eqv (step t x) (step t y) :=
  QPoly.q_add_congr h (Q'.mul_eqv_congr_left _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (square_congr x y h))))

theorem polynomialStep_eval (p : QPoly.Poly) (t : Q') :
    Q'.eqv (QPoly.eval (polynomialStep p) t) (step t (QPoly.eval p t)) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_padd _ _ _)
    (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (QPoly.eval_pscale _ _ _)
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (QPoly.eval_psub _ _ _)
        (QPoly.q_add_congr (eval01 t) (Q'.neg_eqv_congr _ _ (QPoly.eval_pmul p p t)))))))

theorem polynomial_eval (n : Nat) (t : Q') : Q'.eqv (QPoly.eval (polynomial n) t) (iterate t n) := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih => exact Q'.eqv_trans _ _ _ (polynomialStep_eval _ _) (step_congr t _ _ ih)

theorem polynomial_nonnegative (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    (0 : Q')≤QPoly.eval (polynomial n) t :=
  Q'.le_trans' _ _ _ (iterate_invariants t ht h1 n).1 (Q'.ge_of_eqv (polynomial_eval n t))

theorem polynomial_abs_bound (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    Q'.abs (QPoly.eval (polynomial n) t)≤1 := by
  rw [abs_of_nonneg (polynomial_nonnegative n t ht h1)]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval n t)) (iterate_invariants t ht h1 n).2.1

theorem polynomial_uniformCauchy (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : cauchyStage epsilon≤m) (hn : cauchyStage epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (polynomial m) t≤QPoly.eval (polynomial n) t+epsilon ∧
    QPoly.eval (polynomial n) t≤QPoly.eval (polynomial m) t+epsilon := by
  have h := iterate_uniformCauchy epsilon he m n hm hn t ht h1
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval m t))
      (Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (polynomial_eval n t)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (polynomial_eval n t))
      (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (polynomial_eval m t))))⟩

/-- A concrete inhabitant; no root modulus or approximation hypothesis is supplied. -/
def rootSequence : UniformSequence where
  polynomial := polynomial
  modulus := cauchyStage
  cauchy := polynomial_uniformCauchy

def squarePolynomial (n : Nat) : QPoly.Poly := QPoly.pmul (polynomial n) (polynomial n)

theorem squarePolynomial_eval (n : Nat) (t : Q') :
    Q'.eqv (QPoly.eval (squarePolynomial n) t) (iterate t n*iterate t n) :=
  Q'.eqv_trans _ _ _ (QPoly.eval_pmul _ _ _) (square_congr _ _ (polynomial_eval n t))

theorem squarePolynomial_le_coordinate (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (squarePolynomial n) t≤t :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (squarePolynomial_eval n t)) (iterate_invariants t ht h1 n).2.2

theorem coordinate_le_squarePolynomial (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : residualStage epsilon≤n) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    t≤QPoly.eval (squarePolynomial n) t+epsilon :=
  Q'.le_trans' _ _ _ (le_add_of_sub_le (residual_bound t ht h1 epsilon he n hn))
    (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (squarePolynomial_eval n t)))

theorem squarePolynomial_uniformCauchy (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : residualStage epsilon≤m) (hn : residualStage epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (squarePolynomial m) t≤QPoly.eval (squarePolynomial n) t+epsilon ∧
    QPoly.eval (squarePolynomial n) t≤QPoly.eval (squarePolynomial m) t+epsilon :=
  ⟨Q'.le_trans' _ _ _ (squarePolynomial_le_coordinate m t ht h1)
      (coordinate_le_squarePolynomial epsilon he n hn t ht h1),
    Q'.le_trans' _ _ _ (squarePolynomial_le_coordinate n t ht h1)
      (coordinate_le_squarePolynomial epsilon he m hm t ht h1)⟩

def squareSequence : UniformSequence where
  polynomial := squarePolynomial
  modulus := residualStage
  cauchy := squarePolynomial_uniformCauchy

end YMGap.Continuum.UniformSquareRootPolynomial

#print axioms YMGap.Continuum.UniformSquareRootPolynomial.square_congr
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.difference_square_le
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.cauchyStage
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.iterate_tail_difference
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.iterate_uniformCauchy
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.iterateCauchy
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.value
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.valueCauchy
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.value_square
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomialStep
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomial
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.step_congr
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomialStep_eval
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomial_eval
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomial_nonnegative
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomial_abs_bound
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.polynomial_uniformCauchy
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.rootSequence
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.squarePolynomial
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.squarePolynomial_eval
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.squarePolynomial_le_coordinate
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.coordinate_le_squarePolynomial
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.squarePolynomial_uniformCauchy
#print axioms YMGap.Continuum.UniformSquareRootPolynomial.squareSequence
