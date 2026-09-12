/-
# Literal polynomial coefficients of the actual symmetric powers

Every matrix entry is built from the existing fundamental quaternion
polynomials by finite sums and products. Evaluation is proved to recover
the actual symmetric-power action, at every degree and on every matrix
entry. The diagonal sum therefore evaluates to the literal BF4 character
polynomial whenever the evaluated quaternion has unit norm.

The construction retains all raw polynomial coefficients. The proved
identities in this module are EVALUATION identities: they are not
coefficient-probe congruences or Haar identities. In particular, the
unit-norm hypothesis at one environment cannot be inserted into Haar.
Sphere-ideal transport, positive reflected channels, and slab gluing remain
separate obligations. No compactness, spectral gap or continuum claim.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerTrace
import YMGap.Continuum.BF4GeometricSpinNetworkMehler

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial

set_option autoImplicit false

open YMGap.Constructive YMGap.RepTheory
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionTensorPowerAction
open YMGap.Continuum.SU2QuaternionSymmetricPowerAction
open YMGap.Continuum.SU2QuaternionSymmetricPowerTrace
open YMGap.Continuum.BF4GeometricSpinNetworkMehler

local infix:50 " ≃c " => RationalComplexEqv

/-- The polynomial first-row recursion retains every spectator variable. -/
def polynomialFalseRow (q : RatPolyQuaternion) : Nat → (Nat → ComplexRatPoly) → ComplexRatPoly
  | 0, f => f 0
  | m + 1, f => complexRatPolyAdd
      (complexRatPolyMul (fundamentalMatrixCoefficient q false false) (polynomialFalseRow q m f))
      (complexRatPolyMul (fundamentalMatrixCoefficient q false true) (polynomialFalseRow q m (fun j => f (j + 1))))

/-- Literal two-row polynomial readout. This builds no global assignment list. -/
def polynomialRow (q : RatPolyQuaternion) (m : Nat) : Nat → (Nat → ComplexRatPoly) → ComplexRatPoly
  | 0, f => polynomialFalseRow q m f
  | k + 1, f => complexRatPolyAdd
      (complexRatPolyMul (fundamentalMatrixCoefficient q true false) (polynomialRow q m k f))
      (complexRatPolyMul (fundamentalMatrixCoefficient q true true) (polynomialRow q m k (fun j => f (j + 1))))

private theorem eval_mix (rho : Nat → Q') (a b x y : ComplexRatPoly) :
    evalComplexRatPoly rho (complexRatPolyAdd (complexRatPolyMul a x) (complexRatPolyMul b y)) ≃c
      rationalComplexAdd (rationalComplexMul (evalComplexRatPoly rho a) (evalComplexRatPoly rho x))
        (rationalComplexMul (evalComplexRatPoly rho b) (evalComplexRatPoly rho y)) :=
  rationalComplexEqv_trans (evalComplexRatPoly_add rho _ _)
    (rationalComplexAdd_congr (evalComplexRatPoly_mul rho _ _) (evalComplexRatPoly_mul rho _ _))

/-- Evaluation commutes with the literal coefficient recursion and uses
the standard matrix of the evaluated quaternion. -/
theorem eval_polynomialRow (rho : Nat → Q') (q : RatPolyQuaternion) :
    ∀ m k (f : Nat → ComplexRatPoly),
      evalComplexRatPoly rho (polynomialRow q m k f) ≃c
        rowValue (fundamentalMatrixValue (RationalQuaternionRatPoly.eval rho q)) m k
          (fun j => evalComplexRatPoly rho (f j))
  | 0, 0, _ => rationalComplexEqv_refl _
  | m + 1, 0, f => rationalComplexEqv_trans (eval_mix rho _ _ _ _)
      (rationalComplexAdd_congr
        (rationalComplexMul_congr (evaluatedFundamentalMatrix_eq_value rho q false false)
          (eval_polynomialRow rho q m 0 f))
        (rationalComplexMul_congr (evaluatedFundamentalMatrix_eq_value rho q false true)
          (eval_polynomialRow rho q m 0 (fun j => f (j + 1)))))
  | m, k + 1, f => rationalComplexEqv_trans (eval_mix rho _ _ _ _)
      (rationalComplexAdd_congr
        (rationalComplexMul_congr (evaluatedFundamentalMatrix_eq_value rho q true false)
          (eval_polynomialRow rho q m k f))
        (rationalComplexMul_congr (evaluatedFundamentalMatrix_eq_value rho q true true)
          (eval_polynomialRow rho q m k (fun j => f (j + 1)))))

def polynomialBasis (k j : Nat) : ComplexRatPoly :=
  if j = k then complexRatPolyOne else complexRatPolyZero

theorem eval_polynomialBasis (rho : Nat → Q') (k j : Nat) :
    evalComplexRatPoly rho (polynomialBasis k j) ≃c basis k j := by
  by_cases h : j = k
  · simp only [polynomialBasis, basis, h, ↓reduceIte]
    exact evalComplexRatPoly_one rho
  · simp only [polynomialBasis, basis, h, ↓reduceIte]
    exact evalComplexRatPoly_zero rho

/-- The literal polynomial matrix coefficient, row k and column j at degree n.
Only the finite window k,j≤n is a matrix of the representation. -/
def polynomialMatrixCoefficient (q : RatPolyQuaternion) (n k j : Nat) : ComplexRatPoly :=
  polynomialRow q (n - k) k (polynomialBasis j)

/-- Every polynomial matrix coefficient evaluates to the previously
constructed actual action on the explicit basis, not just its trace. -/
theorem eval_polynomialMatrixCoefficient (rho : Nat → Q') (q : RatPolyQuaternion)
    (n k j : Nat) (hk : k ≤ n) :
    evalComplexRatPoly rho (polynomialMatrixCoefficient q n k j) ≃c
      symmetricAction n (RationalQuaternionRatPoly.eval rho q) (basis j) k :=
  rationalComplexEqv_trans (eval_polynomialRow rho q (n - k) k (polynomialBasis j))
    (rationalComplexEqv_trans (rowValue_congr _ _ _ (fun i _ => eval_polynomialBasis rho j i))
      (rationalComplexEqv_symm (coefficient_matrixAction _ n (basis j) k hk)))

def polynomialSum : Nat → (Nat → ComplexRatPoly) → ComplexRatPoly
  | 0, _ => complexRatPolyZero
  | n + 1, f => complexRatPolyAdd (polynomialSum n f) (f n)

theorem eval_polynomialSum (rho : Nat → Q') : ∀ n (f : Nat → ComplexRatPoly),
    evalComplexRatPoly rho (polynomialSum n f) ≃c complexSum n (fun j => evalComplexRatPoly rho (f j))
  | 0, _ => evalComplexRatPoly_zero rho
  | n + 1, f => rationalComplexEqv_trans (evalComplexRatPoly_add rho _ _)
      (rationalComplexAdd_congr (eval_polynomialSum rho n f) (rationalComplexEqv_refl _))

private theorem sum_congr : ∀ n {f g : Nat → RationalComplex},
    (∀ j, j < n → f j ≃c g j) → complexSum n f ≃c complexSum n g
  | 0, _, _, _ => rationalComplexEqv_refl _
  | n + 1, _, _, h => rationalComplexAdd_congr
      (sum_congr n (fun j hj => h j (by omega))) (h n (by omega))

/-- Trace built from the actual polynomial matrix entries in dimension n+1. -/
def polynomialTrace (q : RatPolyQuaternion) (n : Nat) : ComplexRatPoly :=
  polynomialSum (n + 1) (fun k => polynomialMatrixCoefficient q n k k)

theorem eval_polynomialTrace (rho : Nat → Q') (q : RatPolyQuaternion) (n : Nat) :
    evalComplexRatPoly rho (polynomialTrace q n) ≃c
      trace (fundamentalMatrixValue (RationalQuaternionRatPoly.eval rho q)) n :=
  rationalComplexEqv_trans (eval_polynomialSum rho (n + 1) _)
    (sum_congr (n + 1) (fun k hk => eval_polynomialMatrixCoefficient rho q n k k (by omega)))

/-- Evaluation-level link to the ORIGINAL BF4 characterPolynomial, for all
degrees and all polynomial quaternion words evaluating to unit norm.
This is deliberately not a Haar congruence theorem. -/
theorem eval_polynomialTrace_eq_characterPolynomial (rho : Nat → Q') (q : RatPolyQuaternion)
    (hunit : RationalQuaternion.IsUnitNorm (RationalQuaternionRatPoly.eval rho q)) (n : Nat) :
    evalComplexRatPoly rho (polynomialTrace q n) ≃c
      (evalRatPoly rho (characterPolynomial q.r n), 0) :=
  rationalComplexEqv_trans (eval_polynomialTrace rho q n)
    (rationalComplexEqv_trans (trace_eq_cheb ⟨RationalQuaternionRatPoly.eval rho q, hunit⟩ n)
      ⟨Q'.eqv_symm (eval_characterPolynomial rho q.r n), Q'.eqv_refl _⟩)

end YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialFalseRow
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialRow
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialRow
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialBasis
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialBasis
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialMatrixCoefficient
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialMatrixCoefficient
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialSum
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialSum
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.polynomialTrace
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialTrace
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial.eval_polynomialTrace_eq_characterPolynomial
