/-
# Inverse-free local cube adjoint algebra

Two angular derivatives of A cubed times g have an exact factor A. This is
only a polynomial Leibniz identity; it asserts no weighted identity,
positivity, or variance estimate.
-/

import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.QuaternionHaarLocalCubeAdjoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

private def cube (A : RatPoly) : RatPoly := polyMul (polyMul A A) A

private theorem derivative_cube (i j : Nat) (A : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (cube A))
      (polySmul 3 (polyMul (polyMul A A) (angularDerivative i j A))) := by
  let X := angularDerivative i j A
  have h : RatPolyCoeffEqv (angularDerivative i j (cube A))
      (polyAdd
        (polyMul (polyAdd (polyMul X A) (polyMul A X)) A)
        (polyMul (polyMul A A) X)) :=
    (angularDerivative_mul i j (polyMul A A) A).trans
      (((angularDerivative_mul i j A A).mul_right A).add (RatPolyCoeffEqv.refl _))
  have hr : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyAdd (polyMul X A) (polyMul A X)) A)
        (polyMul (polyMul A A) X))
      (polyMul (cap 3) (polyMul (polyMul A A) X)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.mul (.var 1) (.var 0)) (.mul (.var 0) (.var 1))) (.var 0))
        (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (.mul (.const 3) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => A | _ => X)
  exact h.trans (hr.trans (cap_mul_left 3 _))

private theorem first_derivative (i j : Nat) (A g : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (polyMul (cube A) g))
      (polyAdd
        (polyMul (polySmul 3 (polyMul (polyMul A A) (angularDerivative i j A))) g)
        (polyMul (cube A) (angularDerivative i j g))) :=
  (angularDerivative_mul i j (cube A) g).trans
    (((derivative_cube i j A).mul_right g).add (RatPolyCoeffEqv.refl _))

/-- Explicit five-term factor after `Y(X(A³g))`; the order `Y(X A)` and
`Y(X g)` is retained, with no commutation premise. -/
def cubeAdjoint (i j k l : Nat) (A g : RatPoly) : RatPoly :=
  let xA := angularDerivative i j A
  let yA := angularDerivative k l A
  let yxA := angularDerivative k l xA
  let xg := angularDerivative i j g
  let yg := angularDerivative k l g
  let yxg := angularDerivative k l xg
  polyAdd
    (polyMul (cap 6) (polyMul (polyMul xA yA) g))
    (polyAdd
      (polyMul (cap 3) (polyMul (polyMul A yxA) g))
      (polyAdd
        (polyMul (cap 3) (polyMul (polyMul A xA) yg))
        (polyAdd
          (polyMul (cap 3) (polyMul (polyMul A yA) xg))
          (polyMul (polyMul A A) yxg))))

private def expanded (A g xA yA yxA xg yg yxg : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (polySmul 3
        (polyAdd
          (polyMul (polyAdd (polyMul yA A) (polyMul A yA)) xA)
          (polyMul (polyMul A A) yxA))) g)
      (polyMul (polySmul 3 (polyMul (polyMul A A) xA)) yg))
    (polyAdd
      (polyMul (polySmul 3 (polyMul (polyMul A A) yA)) xg)
      (polyMul (cube A) yxg))

private theorem second_derivative_expanded (i j k l : Nat) (A g : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative k l (angularDerivative i j (polyMul (cube A) g)))
      (expanded A g (angularDerivative i j A) (angularDerivative k l A)
        (angularDerivative k l (angularDerivative i j A))
        (angularDerivative i j g) (angularDerivative k l g)
        (angularDerivative k l (angularDerivative i j g))) := by
  let xA := angularDerivative i j A
  let yA := angularDerivative k l A
  let xg := angularDerivative i j g
  let yg := angularDerivative k l g
  have hinner := (angularDerivative_mul k l (polyMul A A) xA).trans
    (((angularDerivative_mul k l A A).mul_right xA).add (RatPolyCoeffEqv.refl _))
  have hscaled := (angularDerivative_smul k l 3 _).trans (hinner.smul 3)
  have hleft : RatPolyCoeffEqv
      (angularDerivative k l
        (polyMul (polySmul 3 (polyMul (polyMul A A) xA)) g))
      (polyAdd
        (polyMul (polySmul 3
          (polyAdd
            (polyMul (polyAdd (polyMul yA A) (polyMul A yA)) xA)
            (polyMul (polyMul A A) (angularDerivative k l xA)))) g)
        (polyMul (polySmul 3 (polyMul (polyMul A A) xA)) yg)) :=
    (angularDerivative_mul k l (polySmul 3 (polyMul (polyMul A A) xA)) g).trans
      ((hscaled.mul_right g).add (RatPolyCoeffEqv.refl _))
  have hright : RatPolyCoeffEqv
      (angularDerivative k l (polyMul (cube A) xg))
      (polyAdd
        (polyMul (polySmul 3 (polyMul (polyMul A A) yA)) xg)
        (polyMul (cube A) (angularDerivative k l xg))) :=
    (angularDerivative_mul k l (cube A) xg).trans
      (((derivative_cube k l A).mul_right xg).add (RatPolyCoeffEqv.refl _))
  exact (angularDerivative_congr k l (first_derivative i j A g)).trans
    ((angularDerivative_add k l _ _).trans (hleft.add hright))

private def expandedCap (A g xA yA yxA xg yg yxg : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (polyMul (cap 3)
        (polyAdd
          (polyMul (polyAdd (polyMul yA A) (polyMul A yA)) xA)
          (polyMul (polyMul A A) yxA))) g)
      (polyMul (polyMul (cap 3) (polyMul (polyMul A A) xA)) yg))
    (polyAdd
      (polyMul (polyMul (cap 3) (polyMul (polyMul A A) yA)) xg)
      (polyMul (cube A) yxg))

private theorem expanded_to_cap (A g xA yA yxA xg yg yxg : RatPoly) :
    RatPolyCoeffEqv (expanded A g xA yA yxA xg yg yxg)
      (expandedCap A g xA yA yxA xg yg yxg) := by
  unfold expanded expandedCap
  exact (((cap_mul_left 3 _).symm.mul_right g).add
    ((cap_mul_left 3 _).symm.mul_right yg)).add
    (((cap_mul_left 3 _).symm.mul_right xg).add (RatPolyCoeffEqv.refl _))

private theorem expandedCap_factor (i j k l : Nat) (A g : RatPoly) :
    RatPolyCoeffEqv
      (expandedCap A g (angularDerivative i j A) (angularDerivative k l A)
        (angularDerivative k l (angularDerivative i j A))
        (angularDerivative i j g) (angularDerivative k l g)
        (angularDerivative k l (angularDerivative i j g)))
      (polyMul A (cubeAdjoint i j k l A g)) := by
  let xA := angularDerivative i j A
  let yA := angularDerivative k l A
  let yxA := angularDerivative k l xA
  let xg := angularDerivative i j g
  let yg := angularDerivative k l g
  let yxg := angularDerivative k l xg
  unfold expandedCap cubeAdjoint cube
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add
        (.mul (.mul (.const 3)
          (.add
            (.mul (.add (.mul (.var 2) (.var 0)) (.mul (.var 0) (.var 2))) (.var 1))
            (.mul (.mul (.var 0) (.var 0)) (.var 3)))) (.var 4))
        (.mul (.mul (.const 3) (.mul (.mul (.var 0) (.var 0)) (.var 1))) (.var 6)))
      (.add
        (.mul (.mul (.const 3) (.mul (.mul (.var 0) (.var 0)) (.var 2))) (.var 5))
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.var 7))))
    (.mul (.var 0)
      (.add
        (.mul (.const 6) (.mul (.mul (.var 1) (.var 2)) (.var 4)))
        (.add
          (.mul (.const 3) (.mul (.mul (.var 0) (.var 3)) (.var 4)))
          (.add
            (.mul (.const 3) (.mul (.mul (.var 0) (.var 1)) (.var 6)))
            (.add
              (.mul (.const 3) (.mul (.mul (.var 0) (.var 2)) (.var 5)))
              (.mul (.mul (.var 0) (.var 0)) (.var 7)))))))
    (by decide)
    (fun | 0 => A | 1 => xA | 2 => yA | 3 => yxA | 4 => g
         | 5 => xg | 6 => yg | _ => yxg)

/-- Exact local factorization `Y(X(A³g)) ≃ A·J`, with no inverse of A. -/
theorem cubeAdjoint_factor (i j k l : Nat) (A g : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative k l
        (angularDerivative i j (polyMul (cube A) g)))
      (polyMul A (cubeAdjoint i j k l A g)) :=
  (second_derivative_expanded i j k l A g).trans
    ((expanded_to_cap A g _ _ _ _ _ _).trans
      (expandedCap_factor i j k l A g))

#print axioms cubeAdjoint
#print axioms cubeAdjoint_factor

end YMGap.Continuum.QuaternionHaarLocalCubeAdjoint
