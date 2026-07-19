/-
# Fundamental trace and whole-word inversion in the quaternion carrier

The elementary-cube contraction may coherently orient its six faces only
after reversing three of the canonical plaquette words.  That operation is
legitimate for the fundamental SU(2) character because the trace of a unit
quaternion and the trace of its inverse agree.

This leaf records that fact in the same honest complex-pair carrier used by
`SU2QuaternionOneLinkFundamentalSchur`.  The diagonal sum of the fundamental
matrix is exactly the rank-one Chebyshev character

    tr D(q) = U_1(q.r) = 2 q.r,

with zero imaginary component.  Quaternion conjugation fixes the scalar
coordinate, so both the raw matrix trace and the evaluated polynomial trace
are invariant under conjugation.  On `UnitNorm`, inversion is conjugation,
which gives the required whole-word reversal theorem.

No plaquette product, cube network, density polynomial, or finite state space
is unfolded here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.ChebyshevBound
import YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics

namespace YMGap.Continuum.SU2QuaternionFundamentalTraceInversion

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.RepTheory

local infix:50 " ≈ " => Q'.eqv

private theorem rationalComplexEqv_symm
    {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    RationalComplexEqv right left :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩

private theorem rationalComplexEqv_trans
    {first second third : RationalComplex}
    (hfirst : RationalComplexEqv first second)
    (hsecond : RationalComplexEqv second third) :
    RationalComplexEqv first third :=
  ⟨Q'.eqv_trans _ _ _ hfirst.1 hsecond.1,
    Q'.eqv_trans _ _ _ hfirst.2 hsecond.2⟩

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_add_self_eqv_two_mul (value : Q') :
    value + value ≈ (2 : Q') * value := by
  exact Q'.eqv_symm (YMGap.Continuum.Cheb.two_mul_eqv value)

/-! ## 1. The raw fundamental trace -/

/-- Trace of a rational-complex fundamental matrix. -/
def fundamentalMatrixTrace
    (matrix : FundamentalMatrix) : RationalComplex :=
  rationalComplexAdd (matrix false false) (matrix true true)

/-- The fundamental trace of a raw quaternion is the real character
`U_1(q.r) = 2 q.r`. -/
theorem fundamentalMatrixTrace_value
    (quaternion : RationalQuaternion) :
    RationalComplexEqv
      (fundamentalMatrixTrace (fundamentalMatrixValue quaternion))
      (YMGap.Continuum.Cheb.U 1 quaternion.r, 0) := by
  unfold fundamentalMatrixTrace fundamentalMatrixValue rationalComplexAdd
    RationalComplexEqv
  constructor
  · simpa only [YMGap.Continuum.Cheb.U_one] using
      (q_add_self_eqv_two_mul quaternion.r)
  · exact Q'.add_neg_self_eqv quaternion.i

/-- Whole-quaternion conjugation leaves the fundamental trace unchanged. -/
theorem fundamentalMatrixTrace_conj
    (quaternion : RationalQuaternion) :
    RationalComplexEqv
      (fundamentalMatrixTrace
        (fundamentalMatrixValue (RationalQuaternion.conj quaternion)))
      (fundamentalMatrixTrace (fundamentalMatrixValue quaternion)) := by
  exact rationalComplexEqv_trans
    (fundamentalMatrixTrace_value
      (RationalQuaternion.conj quaternion))
    (rationalComplexEqv_symm
      (fundamentalMatrixTrace_value quaternion))

/-- On the unit-quaternion carrier, inversion leaves the fundamental trace
unchanged because inverse is quaternion conjugation. -/
theorem unitNormFundamentalMatrixTrace_inv
    (quaternion : RationalQuaternion.UnitNorm) :
    RationalComplexEqv
      (fundamentalMatrixTrace
        (fundamentalMatrixValue
          (RationalQuaternion.UnitNorm.inv quaternion).val))
      (fundamentalMatrixTrace
        (fundamentalMatrixValue quaternion.val)) := by
  simpa [RationalQuaternion.UnitNorm.inv,
    RationalQuaternion.UnitNorm.conj] using
    (fundamentalMatrixTrace_conj quaternion.val)

/-! ## 2. Polynomial trace and evaluated character -/

/-- Addition on the honest complex-pair polynomial carrier. -/
def complexRatPolyAdd
    (left right : ComplexRatPoly) : ComplexRatPoly :=
  (polyAdd left.1 right.1, polyAdd left.2 right.2)

/-- The diagonal sum of the polynomial fundamental matrix. -/
def fundamentalTraceCoefficient
    (quaternion : RatPolyQuaternion) : ComplexRatPoly :=
  complexRatPolyAdd
    (fundamentalMatrixCoefficient quaternion false false)
    (fundamentalMatrixCoefficient quaternion true true)

/-- Evaluation of the polynomial diagonal sum is exactly the rank-one
Chebyshev character of the evaluated quaternion, with zero imaginary part. -/
theorem eval_fundamentalTraceCoefficient_eq_chebOne
    (rho : Nat → Q') (quaternion : RatPolyQuaternion) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (fundamentalTraceCoefficient quaternion))
      (YMGap.Continuum.Cheb.U 1
        (RationalQuaternionRatPoly.eval rho quaternion).r, 0) := by
  unfold fundamentalTraceCoefficient complexRatPolyAdd
    fundamentalMatrixCoefficient evalComplexRatPoly RationalComplexEqv
  constructor
  · change
      evalRatPoly rho (polyAdd quaternion.r quaternion.r) ≈
        YMGap.Continuum.Cheb.U 1 (evalRatPoly rho quaternion.r)
    exact Q'.eqv_trans _
      (evalRatPoly rho quaternion.r + evalRatPoly rho quaternion.r) _
      (evalRatPoly_add rho quaternion.r quaternion.r)
      (by
        simpa only [YMGap.Continuum.Cheb.U_one] using
          (q_add_self_eqv_two_mul (evalRatPoly rho quaternion.r)))
  · change
      evalRatPoly rho (polyAdd quaternion.i (polyNeg quaternion.i)) ≈ 0
    exact Q'.eqv_trans _
      (evalRatPoly rho quaternion.i +
        evalRatPoly rho (polyNeg quaternion.i)) _
      (evalRatPoly_add rho quaternion.i (polyNeg quaternion.i))
      (Q'.eqv_trans _
        (evalRatPoly rho quaternion.i +
          -(evalRatPoly rho quaternion.i)) _
        (q_add_congr (Q'.eqv_refl _)
          (evalRatPoly_neg rho quaternion.i))
        (Q'.add_neg_self_eqv _))

/-- Polynomial quaternion conjugation leaves the evaluated fundamental trace
unchanged in every rational environment. -/
theorem eval_fundamentalTraceCoefficient_conj
    (rho : Nat → Q') (quaternion : RatPolyQuaternion) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (fundamentalTraceCoefficient
          (RationalQuaternionRatPoly.conj quaternion)))
      (evalComplexRatPoly rho
        (fundamentalTraceCoefficient quaternion)) := by
  exact rationalComplexEqv_trans
    (eval_fundamentalTraceCoefficient_eq_chebOne rho
      (RationalQuaternionRatPoly.conj quaternion))
    (rationalComplexEqv_symm
      (eval_fundamentalTraceCoefficient_eq_chebOne rho quaternion))

#print axioms fundamentalMatrixTrace_value
#print axioms fundamentalMatrixTrace_conj
#print axioms unitNormFundamentalMatrixTrace_inv
#print axioms eval_fundamentalTraceCoefficient_eq_chebOne
#print axioms eval_fundamentalTraceCoefficient_conj

end YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
