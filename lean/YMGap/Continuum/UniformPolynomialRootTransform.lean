/-
# Iteratable root transformation of explicit interval polynomial sequences

For polynomial stages P_n taking [0,1] into [0,1], apply the proved
n-th root polynomial to P_n. Uniform Cauchy data for P, plus the uniform
root residual estimate, construct Cauchy data for this diagonal sequence.
The estimate a^2<=b^2+epsilon^2 => a<=b+epsilon on the nonnegative cone
needs no positive lower spectral bound. The transformed stages remain in
[0,1], so the construction can be iterated without a new analytic input.
Their squares converge uniformly to the original sequence P.

This is polynomial data and quantitative approximation, not yet the
original operator square identity, continuous time or a physical gap.
-/

import YMGap.Continuum.UniformSquareRootPolynomial
import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

namespace YMGap.Continuum.UniformPolynomialRootTransform

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BernsteinUniformConvergence (abs_of_nonneg)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra (compose eval_compose)
open YMGap.Continuum.UniformSquareRootIteration (iterate iterate_invariants residualStage residual_bound)
open YMGap.Continuum.UniformSquareRootPolynomial (polynomial polynomial_eval square_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction (UniformSequence)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility (half_error_trans)

/-- Ordinary explicit approximation data; not a physical frontier or a supplied operator root. -/
structure IntervalSequence where
  sequence : UniformSequence
  bounds : ∀ n,∀ t : Q',(0 : Q')≤t → t≤1 →
    (0 : Q')≤QPoly.eval (sequence.polynomial n) t ∧ QPoly.eval (sequence.polynomial n) t≤1

theorem square_error (a b epsilon : Q') (ha : (0 : Q')≤a) (hb : (0 : Q')≤b)
    (he : (0 : Q')<epsilon) (h : a*a≤b*b+epsilon*epsilon) : a≤b+epsilon := by
  have hpos : (0 : Q')<b+epsilon := Q'.pos_of_lt_of_le he
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg epsilon b hb) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  apply le_of_sq_le_sq hpos ha
  have hc : (0 : Q')≤2*b*epsilon :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q')≤2) hb) (Q'.le_of_lt he)
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hc)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.const 2) (.var 0)) (.var 1)))
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (by decide) (fun | 0 => b | _ => epsilon))))

def transformedPolynomial (P : IntervalSequence) (n : Nat) : QPoly.Poly :=
  compose (P.sequence.polynomial n) (polynomial n)

theorem transformed_eval (P : IntervalSequence) (n : Nat) (t : Q') :
    Q'.eqv (QPoly.eval (transformedPolynomial P n) t) (iterate (QPoly.eval (P.sequence.polynomial n) t) n) :=
  Q'.eqv_trans _ _ _ (eval_compose _ _ _) (polynomial_eval _ _)

theorem transformed_bounds (P : IntervalSequence) (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    (0 : Q')≤QPoly.eval (transformedPolynomial P n) t ∧ QPoly.eval (transformedPolynomial P n) t≤1 := by
  have h := iterate_invariants _ (P.bounds n t ht h1).1 (P.bounds n t ht h1).2 n
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (transformed_eval P n t)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (transformed_eval P n t)) h.2.1⟩

theorem transformed_square_le (P : IntervalSequence) (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (transformedPolynomial P n) t*QPoly.eval (transformedPolynomial P n) t≤
      QPoly.eval (P.sequence.polynomial n) t :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (square_congr _ _ (transformed_eval P n t)))
    (iterate_invariants _ (P.bounds n t ht h1).1 (P.bounds n t ht h1).2 n).2.2

theorem transformed_square_error (P : IntervalSequence) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : residualStage epsilon≤n) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (P.sequence.polynomial n) t≤
      QPoly.eval (transformedPolynomial P n) t*QPoly.eval (transformedPolynomial P n) t+epsilon :=
  Q'.le_trans' _ _ _ (le_add_of_sub_le
    (residual_bound _ (P.bounds n t ht h1).1 (P.bounds n t ht h1).2 epsilon he n hn))
    (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (square_congr _ _ (transformed_eval P n t))))

def rootModulus (P : IntervalSequence) (epsilon : Q') : Nat :=
  max (P.sequence.modulus (HalfPow.half*(epsilon*epsilon))) (residualStage (HalfPow.half*(epsilon*epsilon)))

theorem transformed_uniformCauchy (P : IntervalSequence) (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : rootModulus P epsilon≤m) (hn : rootModulus P epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (transformedPolynomial P m) t≤QPoly.eval (transformedPolynomial P n) t+epsilon ∧
    QPoly.eval (transformedPolynomial P n) t≤QPoly.eval (transformedPolynomial P m) t+epsilon := by
  let d := HalfPow.half*(epsilon*epsilon)
  have hd : (0 : Q')<d := Q'.mul_pos (by decide : (0 : Q')<HalfPow.half) (Q'.mul_pos he he)
  have hs := P.sequence.cauchy d hd m n (Nat.le_trans (Nat.le_max_left _ _) hm)
    (Nat.le_trans (Nat.le_max_left _ _) hn) t ht h1
  have hmerr := transformed_square_error P d hd m (Nat.le_trans (Nat.le_max_right _ _) hm) t ht h1
  have hnerr := transformed_square_error P d hd n (Nat.le_trans (Nat.le_max_right _ _) hn) t ht h1
  exact ⟨square_error _ _ epsilon (transformed_bounds P m t ht h1).1 (transformed_bounds P n t ht h1).1 he
      (half_error_trans _ _ _ (epsilon*epsilon) (Q'.le_trans' _ _ _ (transformed_square_le P m t ht h1) hs.1) hnerr),
    square_error _ _ epsilon (transformed_bounds P n t ht h1).1 (transformed_bounds P m t ht h1).1 he
      (half_error_trans _ _ _ (epsilon*epsilon) (Q'.le_trans' _ _ _ (transformed_square_le P n t ht h1) hs.2) hmerr)⟩

/-- The output has the SAME input type, allowing arbitrary finite repeated roots. -/
def rootTransform (P : IntervalSequence) : IntervalSequence where
  sequence := ⟨transformedPolynomial P,rootModulus P,transformed_uniformCauchy P⟩
  bounds := transformed_bounds P

theorem rootTransform_abs_bound (P : IntervalSequence) (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    Q'.abs (QPoly.eval ((rootTransform P).sequence.polynomial n) t)≤1 := by
  rw [abs_of_nonneg ((rootTransform P).bounds n t ht h1).1]
  exact ((rootTransform P).bounds n t ht h1).2

def transformedSquare (P : IntervalSequence) (n : Nat) : QPoly.Poly :=
  QPoly.pmul (transformedPolynomial P n) (transformedPolynomial P n)

theorem transformedSquare_le (P : IntervalSequence) (n : Nat) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (transformedSquare P n) t≤QPoly.eval (P.sequence.polynomial n) t :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (QPoly.eval_pmul _ _ _)) (transformed_square_le P n t ht h1)

theorem transformedSquare_error (P : IntervalSequence) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : residualStage epsilon≤n) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (P.sequence.polynomial n) t≤QPoly.eval (transformedSquare P n) t+epsilon :=
  Q'.le_trans' _ _ _ (transformed_square_error P epsilon he n hn t ht h1)
    (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (QPoly.eval_pmul _ _ _)))

def squareModulus (P : IntervalSequence) (epsilon : Q') : Nat :=
  max (P.sequence.modulus (HalfPow.half*epsilon)) (residualStage (HalfPow.half*epsilon))

theorem transformedSquare_uniformCauchy (P : IntervalSequence) (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : squareModulus P epsilon≤m) (hn : squareModulus P epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (transformedSquare P m) t≤QPoly.eval (transformedSquare P n) t+epsilon ∧
    QPoly.eval (transformedSquare P n) t≤QPoly.eval (transformedSquare P m) t+epsilon := by
  let d := HalfPow.half*epsilon
  have hd : (0 : Q')<d := ExpNeg.half_mul_pos epsilon he
  have hs := P.sequence.cauchy d hd m n (Nat.le_trans (Nat.le_max_left _ _) hm)
    (Nat.le_trans (Nat.le_max_left _ _) hn) t ht h1
  exact ⟨half_error_trans _ _ _ epsilon (Q'.le_trans' _ _ _ (transformedSquare_le P m t ht h1) hs.1)
      (transformedSquare_error P d hd n (Nat.le_trans (Nat.le_max_right _ _) hn) t ht h1),
    half_error_trans _ _ _ epsilon (Q'.le_trans' _ _ _ (transformedSquare_le P n t ht h1) hs.2)
      (transformedSquare_error P d hd m (Nat.le_trans (Nat.le_max_right _ _) hm) t ht h1)⟩

def squareSequence (P : IntervalSequence) : UniformSequence :=
  ⟨transformedSquare P,squareModulus P,transformedSquare_uniformCauchy P⟩

end YMGap.Continuum.UniformPolynomialRootTransform

#print axioms YMGap.Continuum.UniformPolynomialRootTransform.IntervalSequence
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.square_error
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformedPolynomial
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformed_eval
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformed_bounds
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformed_square_le
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformed_square_error
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.rootModulus
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformed_uniformCauchy
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.rootTransform
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.rootTransform_abs_bound
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformedSquare
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformedSquare_le
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformedSquare_error
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.squareModulus
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.transformedSquare_uniformCauchy
#print axioms YMGap.Continuum.UniformPolynomialRootTransform.squareSequence
