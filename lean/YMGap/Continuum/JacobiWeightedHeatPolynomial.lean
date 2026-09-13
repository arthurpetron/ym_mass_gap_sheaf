/-
# The finite Jacobi approximant IS the weighted original heat polynomial

The existing finite differentiated identity, initially stated on x>=-1,
is reflected to coefficient equality using a finite rational grid. Actual
multivariate substitution then identifies the positive shifted Jacobi
polynomial with the ORIGINAL character polynomials and heat coefficients,
weighted by the actual finite centered q-binomial/Euler weights.

This is a coefficient-level identity valid under arbitrary Haar insertions,
not an inference from pointwise Haar order. STATUS UPDATE (2026-09-12):
BF4ExactSlabOriginalActionStrictFloor now removes these weights with a
quantified polynomial/Haar estimate, proves a positive original action-limit
floor and the completed full unit non-null. Physical vacuum/gap remain open.
-/

import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
import YMGap.Continuum.JacobiShiftedPositiveCoefficients
import YMGap.Continuum.FiniteJacobiDerivativeIdentity
import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail

namespace YMGap.Continuum.JacobiWeightedHeatPolynomial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialExtensionalReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion
open YMGap.Continuum.QPolyHaarPositiveSubstitution
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra

local infix:50 " ≈ " => Q'.eqv

/-- Actual centered finite Jacobi weight, with its original label shift. -/
def weight (w : Q') (N r : Nat) : Q' := GaussQBinomEulerQuotient.centeredWeight (w * w) N (r + 1)

/-- Bare univariate polynomial with the ORIGINAL heat coefficients. -/
def weightedHeat (w : Q') (N : Nat) : Poly :=
  polyFinSum (fun r => pscale (weight w N r * coeffW w r) (chebPoly r)) N

/-- Original multivariate characters, without altering or commuting the
underlying quaternion word. N is a term count, not the original cutoff K. -/
def weightedPolynomial (w : Q') (N : Nat) (x : RatPoly) : RatPoly :=
  finitePolySum (fun r => polySmul (weight w N r)
    (polySmul (coeffW w r) (characterPolynomial x r))) (List.range N)

private theorem scale_sum (c : Q') (f : Nat → Q') : ∀ N,
    c * finSum f N ≈ finSum (fun r => c * f r) N
  | 0 => Q'.mul_zero_eqv c
  | N + 1 => Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.add_eqv_congr_right _ _ _ (scale_sum c f N))

theorem eval_weightedHeat (w x : Q') (N : Nat) :
    eval (weightedHeat w N) x ≈ finSum (fun r => weight w N r * pointwiseHeatTerm w x r) N :=
  Q'.eqv_trans _ _ _ (eval_polyFinSum _ x N)
    (finSum_congr_eqv (fun r => Q'.eqv_trans _ _ _ (eval_pscale _ _ x)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_chebPoly r x)) (Q'.mul_assoc_eqv _ _ _))) N)

/-- The nome normalization is exactly the existing n(n+2)+1=(n+1)^2 pin. -/
theorem nome_mul_eval_weightedHeat (w x : Q') (N : Nat) :
    w * eval (weightedHeat w N) x ≈
      finSum (fun r => weight w N r * JTPIdentity.dTerm w x r) N :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (eval_weightedHeat w x N))
    (Q'.eqv_trans _ _ _ (scale_sum _ _ N)
      (finSum_congr_eqv (fun r => Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
            (Q'.mul_eqv_congr_left _ _ _ (nome_mul_pointwiseHeatTerm_eqv_dTerm w x r))))) N))

private theorem eval_arg {x y : Q'} (h : x ≈ y) : ∀ p : Poly, eval p x ≈ eval p y
  | [] => Q'.eqv_refl 0
  | c :: p => Q'.add_eqv_congr_left c _ _ (Cheb.mul_eqv_congr _ _ _ _ h (eval_arg h p))

private theorem eval_one_add (x : Q') : eval [1, 1] x ≈ 1 + x :=
  Q'.add_eqv_congr_left 1 _ _
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_zero_eqv x)) (q_add_zero_eqv 1)))
      (Q'.mul_one_eqv x))

private theorem half_two_cancel (a : Q') : HalfPow.half * ((2 : Q') * a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : HalfPow.half * (2 : Q') ≈ 1))
      (Q'.one_mul_eqv a))

private theorem nome_cancel {w : Q'} (hw : (0 : Q') < w) (a : Q') : inverseNome w * (w * a) ≈ a :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inverseNome_mul_nome_eqv hw)) (Q'.one_mul_eqv a))

/-- A finite coefficient identity, not a common-limit or analytic premise.
The half-line domain restriction of the existing derivative theorem is
removed ONLY after representing both sides by genuine finite polynomials. -/
theorem shiftedHeat_polyEqv_weightedHeat {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    PolyEqv (compose [1, 1] (JacobiShiftedPositiveCoefficients.heat w N)) (weightedHeat w N) := by
  apply polyEqv_of_ge_neg_one
  intro x hx
  have he := Q'.eqv_trans _ _ _ (eval_compose [1, 1] x _)
    (Q'.eqv_trans _ _ _ (eval_arg (eval_one_add x) _)
      (JacobiShiftedPositiveCoefficients.eval_heat w x N))
  have hd := FiniteJacobiDerivativeIdentity.fullProdDx_eq_two_weighted_dPartial hw0 hw1 hx N
  have hn := nome_mul_eval_weightedHeat w x N
  exact Q'.eqv_trans _ _ _ he
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hd))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (half_two_cancel _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hn)) (nome_cancel hw0 _))))

/-- The existing kernel coefficient test is proved, not asserted or sampled. -/
theorem shiftedHeat_coefficients {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    allZero (psub (compose [1, 1] (JacobiShiftedPositiveCoefficients.heat w N)) (weightedHeat w N)) :=
  allZero_psub_of_polyEqv (shiftedHeat_polyEqv_weightedHeat hw0 hw1 N)

private theorem sum_append {A : Type} (f : A → RatPoly) : ∀ xs ys : List A,
    finitePolySum f (xs ++ ys) = polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by simp only [List.cons_append, finitePolySum, sum_append f xs ys, polyAdd, List.append_assoc]

/-- Substitution yields the literal weighted ORIGINAL multivariate terms. -/
theorem subst_weightedHeat (w : Q') (N : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (subst x (weightedHeat w N)) (weightedPolynomial w N x) := by
  have h : ∀ M, RatPolyCoeffEqv
      (subst x (polyFinSum (fun r => pscale (weight w N r * coeffW w r) (chebPoly r)) M))
      (finitePolySum (fun r => polySmul (weight w N r)
        (polySmul (coeffW w r) (characterPolynomial x r))) (List.range M)) := by
    intro M
    induction M with
    | zero => exact RatPolyCoeffEqv.refl _
    | succ M ih =>
        rw [List.range_succ, sum_append]
        have hsingle : finitePolySum (fun r => polySmul (weight w N r)
            (polySmul (coeffW w r) (characterPolynomial x r))) [M]
            = polySmul (weight w N M) (polySmul (coeffW w M) (characterPolynomial x M)) := by
          simp only [finitePolySum, polyAdd, polyZero, List.append_nil]
        rw [hsingle]
        exact (subst_padd x _ _).trans
          (ih.add ((subst_pscale x _ _).trans
            (((subst_chebPoly x M).smul _).trans (RatPolyCoeffEqv.smul_assoc _ _ _).symm)))
  exact h N

/-- Main pin: exact coefficients after ANY multivariate substitution.
Every original monomial probe, and hence arbitrary-insertion Haar, sees
the same polynomial. No independence or pointwise-order assumption. -/
theorem shiftedHeat_subst_coeffEqv_weightedPolynomial {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) (x : RatPoly) :
    RatPolyCoeffEqv
      (subst (polyAdd polyOne x) (JacobiShiftedPositiveCoefficients.heat w N))
      (weightedPolynomial w N x) :=
  ((subst_compose x [1, 1] _).trans (subst_arg (subst_one_add x) _)).symm.trans
    ((subst_polyEqv x (shiftedHeat_polyEqv_weightedHeat hw0 hw1 N)).trans (subst_weightedHeat w N x))

end YMGap.Continuum.JacobiWeightedHeatPolynomial

#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.weight
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.weightedHeat
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.weightedPolynomial
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.eval_weightedHeat
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.nome_mul_eval_weightedHeat
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.shiftedHeat_polyEqv_weightedHeat
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.shiftedHeat_coefficients
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.subst_weightedHeat
#print axioms YMGap.Continuum.JacobiWeightedHeatPolynomial.shiftedHeat_subst_coeffEqv_weightedPolynomial
