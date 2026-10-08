/-
# Exact finite Horner chain rules for actual angular derivations

The jets below belong to the literal substituted finite polynomial. Both
ordinary angular planes and the existing plus-paired directions are actual
derivations; no chain-rule or jet-identification premise is supplied.
This is a finite algebraic join, not a differentiated limit or a group flow.
-/

import YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
import YMGap.Continuum.SU2QuaternionPairedFrameScalarJets
import YMGap.Continuum.ChebyshevFormalJets

namespace YMGap.Continuum.QPolyHaarAngularChain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyRatPolySubstitutionAlgebra
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem horner_coeff (c : Q') (p : Poly) :
    CoeffEqv (c::p) (padd [c] (pmul [0,1] p)) := by
  apply ChebyshevFormalJets.coefficients_of_eval_eqv
  intro x
  have hc : QPoly.eval [c] x ≈ c :=
    poly_identity_of_normal_eq (.add (.var 0) (.mul (.var 1) (.const 0)))
      (.var 0) (by decide) (fun | 0 => c | _ => x)
  have hx : QPoly.eval [0,1] x ≈ x :=
    poly_identity_of_normal_eq
      (.add (.const 0) (.mul (.var 0) (.add (.const 1) (.mul (.var 0) (.const 0)))))
      (.var 0) (by decide) (fun _ => x)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (eval_padd _ _ x)
    (Q'.add_eqv_congr' hc (Q'.eqv_trans _ _ _ (eval_pmul _ _ x)
      (Q'.mul_eqv_congr_right _ _ _ hx))))

private theorem subst_variable (x : RatPoly) :
    RatPolyCoeffEqv (subst x [0,1]) x :=
  (subst_zero_cons x [1]).trans
    ((((subst_singleton x 1).trans (RatPolyCoeffEqv.one_smul polyOne)).mul_left x).trans
      (RatPolyCoeffEqv.mul_one x))

private theorem subst_derivative_variable (x : RatPoly) :
    RatPolyCoeffEqv (subst x (pderiv [0,1])) polyOne :=
  (subst_singleton x (1*1)).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.one_mul_eqv 1) polyOne).trans
      (RatPolyCoeffEqv.one_smul polyOne))

/-- Actual finite formal derivative of a Horner cell, after substitution. -/
theorem subst_derivative_horner (x : RatPoly) (c : Q') (p : Poly) :
    RatPolyCoeffEqv (subst x (pderiv (c::p)))
      (polyAdd (subst x p) (polyMul x (subst x (pderiv p)))) := by
  have h := (horner_coeff c p).pderiv.trans
    ((pderiv_padd [c] (pmul [0,1] p)).trans
      ((CoeffEqv.refl (pderiv [c])).padd (pderiv_pmul [0,1] p)))
  refine (subst_polyEqv x (fun y => QPolyCoefficientEvaluation.coefficient_eval h y)).trans ?_
  refine (subst_padd x (pderiv [c]) _).trans ?_
  refine ((RatPolyCoeffEqv.refl polyZero).add
    ((subst_padd x _ _).trans ?_)).trans (RatPolyCoeffEqv.zero_add _)
  exact ((subst_pmul x (pderiv [0,1]) p).trans
    (((subst_derivative_variable x).mul_right _).trans (RatPolyCoeffEqv.one_mul _))).add
    ((subst_pmul x [0,1] (pderiv p)).trans ((subst_variable x).mul_right _))

/-- Every actual angular plane obeys the finite Horner chain rule. -/
theorem angular_subst (i j : Nat) (x : RatPoly) : ∀ p : Poly,
    RatPolyCoeffEqv (angularDerivative i j (subst x p))
      (polyMul (subst x (pderiv p)) (angularDerivative i j x))
  | [] => (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
      (((angularDerivative_smul i j 0 polyOne).trans
        (RatPolyCoeffEqv.zero_smul _)).trans (RatPolyCoeffEqv.mul_zero_left _).symm)
  | c::p => by
    have hc : RatPolyCoeffEqv (angularDerivative i j (polySmul c polyOne)) polyZero :=
      (angularDerivative_smul i j c polyOne).trans
        (((angularDerivative_one i j).smul c).trans (RatPolyCoeffEqv.smul_zero c))
    have h := (angularDerivative_add i j _ _).trans
      (hc.add ((angularDerivative_mul i j x (subst x p)).trans
        ((RatPolyCoeffEqv.refl _).add ((angular_subst i j x p).mul_left x))))
    refine h.trans ((RatPolyCoeffEqv.zero_add _).trans ?_)
    refine (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 0))))
      (.mul (.add (.var 1) (.mul (.var 2) (.var 3))) (.var 0))
      (by decide) (fun
        | 0 => angularDerivative i j x
        | 1 => subst x p
        | 2 => x
        | _ => subst x (pderiv p))).trans ?_
    exact ((subst_derivative_horner x c p).mul_right _).symm

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- The literal plus-paired derivations preserve coefficient equality. -/
theorem paired_congr (i : Fin 3) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (pairedDerivative i p) (pairedDerivative i q) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact (angularDerivative_congr 0 1 h).add (angularDerivative_congr 2 3 h)
  · exact (angularDerivative_congr 0 2 h).add (RatPolyCoeffEqv.neg (angularDerivative_congr 1 3 h))
  · exact (angularDerivative_congr 0 3 h).add (angularDerivative_congr 1 2 h)

/-- Leibniz for the existing paired directions, not a new formal jet. -/
theorem paired_mul (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (polyMul p q))
      (polyAdd (polyMul (pairedDerivative i p) q) (polyMul p (pairedDerivative i q))) := by
  have hp (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul a q) (polyMul p b))
        (polyAdd (polyMul c q) (polyMul p d)))
      (polyAdd (polyMul (polyAdd a c) q) (polyMul p (polyAdd b d))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 1)))
        (.add (.mul (.var 2) (.var 4)) (.mul (.var 5) (.var 3))))
      (.add (.mul (.add (.var 0) (.var 2)) (.var 4))
        (.mul (.var 5) (.add (.var 1) (.var 3))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => q | _ => p)
  have hm (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul a q) (polyMul p b))
        (polyNeg (polyAdd (polyMul c q) (polyMul p d))))
      (polyAdd (polyMul (polyAdd a (polyNeg c)) q)
        (polyMul p (polyAdd b (polyNeg d)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 1)))
        (.neg (.add (.mul (.var 2) (.var 4)) (.mul (.var 5) (.var 3)))))
      (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 4))
        (.mul (.var 5) (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => q | _ => p)
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_mul 0 1 p q).add (angularDerivative_mul 2 3 p q)).trans
      (hp _ _ _ _)
  · exact ((angularDerivative_mul 0 2 p q).add
      (RatPolyCoeffEqv.neg (angularDerivative_mul 1 3 p q))).trans (hm _ _ _ _)
  · exact ((angularDerivative_mul 0 3 p q).add (angularDerivative_mul 1 2 p q)).trans
      (hp _ _ _ _)

/-- Literal first paired jet of any finite substituted polynomial. -/
theorem paired_subst (i : Fin 3) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (pairedDerivative i (subst x p))
      (polyMul (subst x (pderiv p)) (pairedDerivative i x)) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angular_subst 0 1 x p).add (angular_subst 2 3 x p)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _).symm
  · exact ((angular_subst 0 2 x p).add (RatPolyCoeffEqv.neg (angular_subst 1 3 x p))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => subst x (pderiv p)
          | 1 => angularDerivative 0 2 x
          | _ => angularDerivative 1 3 x))
  · exact ((angular_subst 0 3 x p).add (angular_subst 1 2 x p)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _).symm

/-- Actual repeated paired jet, retaining the scalar acceleration term. -/
theorem paired_subst_second (i : Fin 3) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative i (subst x p)))
      (polyAdd
        (polyMul (subst x (pderiv (pderiv p)))
          (polyMul (pairedDerivative i x) (pairedDerivative i x)))
        (polyMul (subst x (pderiv p)) (pairedDerivative i (pairedDerivative i x)))) := by
  refine (paired_congr i (paired_subst i x p)).trans ((paired_mul i _ _).trans ?_)
  exact (((paired_subst i x (pderiv p)).mul_right _).trans
    (RatPolyCoeffEqv.mul_assoc _ _ _)).add (RatPolyCoeffEqv.refl _)

end YMGap.Continuum.QPolyHaarAngularChain

#print axioms YMGap.Continuum.QPolyHaarAngularChain.subst_derivative_horner
#print axioms YMGap.Continuum.QPolyHaarAngularChain.angular_subst
#print axioms YMGap.Continuum.QPolyHaarAngularChain.paired_congr
#print axioms YMGap.Continuum.QPolyHaarAngularChain.paired_mul
#print axioms YMGap.Continuum.QPolyHaarAngularChain.paired_subst
#print axioms YMGap.Continuum.QPolyHaarAngularChain.paired_subst_second
