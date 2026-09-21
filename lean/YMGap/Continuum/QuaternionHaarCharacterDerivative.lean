/-
# Positive character expansion for angular differentiation

The derivative polynomial is constructed by the positive parity recurrence
P_0=0, P_1=2, P_(n+2)=P_n+2(n+2)U_(n+1).  Its coefficient identity with
the actual angular derivative retains every original polynomial variable.
This is an algebraic input for Haar score estimates, not a score bound or
a statement uniform in the heat nome.
-/

import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval
import YMGap.Continuum.SU2CharacterDerivativeCubicBudget

namespace YMGap.Continuum.QuaternionHaarCharacterDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarChebyshevEnergy
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval
open YMGap.Continuum.SU2CharacterDerivativeCubicBudget

private def sub (p q : RatPoly) : RatPoly := polyAdd p (polyNeg q)
private def esub (p q : PolyExpr) : PolyExpr := .add p (.neg q)
private def env (x a b u v k : RatPoly) : Nat → RatPoly
  | 0 => x | 1 => a | 2 => b | 3 => u | 4 => v | _ => k

/-- A positive, finite lower-character expansion of U'_n. -/
def derivativePolynomial (x : RatPoly) : Nat → RatPoly
  | 0 => cap 0
  | 1 => cap 2
  | n+2 => polyAdd (derivativePolynomial x n)
      (polyMul (cap 2)
        (polyMul (cap (Q'.ofNat (n+2))) (characterPolynomial x (n+1))))

private theorem nat_cap_succ (n : Nat) :
    RatPolyCoeffEqv (cap (Q'.ofNat (n+1)))
      (polyAdd (cap (Q'.ofNat n)) (cap 1)) :=
  (RatPolyCoeffEqv.smul_coefficient (Q'.ofNat_add_eqv n 1) polyOne).trans
    (cap_add (Q'.ofNat n) 1).symm

private theorem first_step (x a b u v k : RatPoly) :
    RatPolyCoeffEqv
      (sub (polyMul x (polyAdd a (polyMul (cap 2) (polyMul k v)))) b)
      (polyAdd (sub (polyMul x a) b)
        (polyMul (cap 2) (polyMul k (polyMul x v)))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (esub (.mul (.var 0) (.add (.var 1) (.mul (.const 2) (.mul (.var 5) (.var 4))))) (.var 2))
    (.add (esub (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.const 2) (.mul (.var 5) (.mul (.var 0) (.var 4)))))
    (by decide) (env x a b u v k)

private theorem first_finish (x u v k : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyNeg (polyMul k u))
        (polyMul (cap 2) (polyMul k (polyMul x v))))
      (polyMul k (step x u v)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.neg (.mul (.var 5) (.var 3)))
      (.mul (.const 2) (.mul (.var 5) (.mul (.var 0) (.var 4)))))
    (.mul (.var 5) (.add (.mul (.mul (.const 2) (.var 0)) (.var 4))
      (.mul (.const (-1)) (.var 3))))
    (by decide) (env x polyZero polyZero u v k)

private theorem second_step (x a b v k : RatPoly) :
    RatPolyCoeffEqv
      (sub (polyMul x b) (polyAdd a (polyMul (cap 2) (polyMul k v))))
      (sub (sub (polyMul x b) a) (polyMul (cap 2) (polyMul k v))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (esub (.mul (.var 0) (.var 2)) (.add (.var 1) (.mul (.const 2) (.mul (.var 5) (.var 4)))))
    (esub (esub (.mul (.var 0) (.var 2)) (.var 1)) (.mul (.const 2) (.mul (.var 5) (.var 4))))
    (by decide) (env x a b polyZero v k)

private theorem second_finish (v k : RatPoly) :
    RatPolyCoeffEqv
      (sub (polyMul k v)
        (polyMul (cap 2) (polyMul (polyAdd k (cap 1)) v)))
      (polyNeg (polyMul (polyAdd (polyAdd k (cap 1)) (cap 1)) v)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (esub (.mul (.var 5) (.var 4))
      (.mul (.const 2) (.mul (.add (.var 5) (.const 1)) (.var 4))))
    (.neg (.mul (.add (.add (.var 5) (.const 1)) (.const 1)) (.var 4)))
    (by decide) (env polyZero polyZero polyZero polyZero v k)

private theorem derivative_pair (x : RatPoly) : ∀ n : Nat,
    RatPolyCoeffEqv
      (sub (polyMul x (derivativePolynomial x (n+1))) (derivativePolynomial x n))
      (polyMul (cap (Q'.ofNat (n+1))) (characterPolynomial x (n+1))) ∧
    RatPolyCoeffEqv
      (sub (polyMul x (derivativePolynomial x n)) (derivativePolynomial x (n+1)))
      (polyNeg (polyMul (cap (Q'.ofNat (n+2))) (characterPolynomial x n)))
  | 0 => by
      constructor
      · exact (coeffEvalExpr_eqv_of_normalize_eq
          (esub (.mul (.var 0) (.const 2)) (.const 0))
          (.mul (.const 1) (.mul (.const 2) (.var 0))) (by decide) (fun _ => x)).trans
            ((cap_mul_left 2 x).mul_left (cap 1))
      · exact (coeffEvalExpr_eqv_of_normalize_eq
          (esub (.mul (.var 0) (.const 0)) (.const 2))
          (.neg (.mul (.const 2) (.const 1))) (by decide) (fun _ => x)).trans
            (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.one_smul polyOne).mul_left (cap 2)))
  | n+1 => by
      obtain ⟨hfirst, hsecond⟩ := derivative_pair x n
      constructor
      · refine (first_step x (derivativePolynomial x n) (derivativePolynomial x (n+1))
          (characterPolynomial x n) (characterPolynomial x (n+1)) (cap (Q'.ofNat (n+2)))).trans ?_
        refine (hsecond.add (RatPolyCoeffEqv.refl _)).trans ?_
        refine (first_finish x (characterPolynomial x n) (characterPolynomial x (n+1))
          (cap (Q'.ofNat (n+2)))).trans ?_
        exact (character_step_pin x n).symm.mul_left (cap (Q'.ofNat (n+2)))
      · refine (second_step x (derivativePolynomial x n) (derivativePolynomial x (n+1))
          (characterPolynomial x (n+1)) (cap (Q'.ofNat (n+2)))).trans ?_
        refine (hfirst.add (RatPolyCoeffEqv.neg
          (((nat_cap_succ (n+1)).mul_right (characterPolynomial x (n+1))).mul_left (cap 2)))).trans ?_
        refine (second_finish (characterPolynomial x (n+1)) (cap (Q'.ofNat (n+1)))).trans ?_
        exact RatPolyCoeffEqv.neg
          ((((nat_cap_succ (n+1)).add (RatPolyCoeffEqv.refl _)).symm.trans
            (nat_cap_succ (n+2)).symm).mul_right (characterPolynomial x (n+1)))

private def derivativeStep (x a b u : RatPoly) : RatPoly :=
  polyAdd (polyMul (cap 2) u) (step x a b)

private theorem recurrence_start (x a b u : RatPoly) :
    RatPolyCoeffEqv (derivativeStep x a b u)
      (polyAdd a (polyAdd (polyMul (cap 2) (sub (polyMul x b) a))
        (polyMul (cap 2) u))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.const 2) (.var 3))
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.mul (.const (-1)) (.var 1))))
    (.add (.var 1) (.add (.mul (.const 2) (esub (.mul (.var 0) (.var 2)) (.var 1)))
      (.mul (.const 2) (.var 3)))) (by decide) (env x a b u polyZero polyZero)

private theorem recurrence_finish (a u k : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd a (polyAdd (polyMul (cap 2) (polyMul k u)) (polyMul (cap 2) u)))
      (polyAdd a (polyMul (cap 2) (polyMul (polyAdd k (cap 1)) u))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 1) (.add (.mul (.const 2) (.mul (.var 5) (.var 3))) (.mul (.const 2) (.var 3))))
    (.add (.var 1) (.mul (.const 2) (.mul (.add (.var 5) (.const 1)) (.var 3))))
    (by decide) (env polyZero a polyZero u polyZero k)

private theorem derivative_recurrence (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv
      (derivativeStep x (derivativePolynomial x n) (derivativePolynomial x (n+1))
        (characterPolynomial x (n+1))) (derivativePolynomial x (n+2)) := by
  refine (recurrence_start x (derivativePolynomial x n) (derivativePolynomial x (n+1))
    (characterPolynomial x (n+1))).trans ?_
  refine ((RatPolyCoeffEqv.refl _).add
    ((((derivative_pair x n).1).mul_left (cap 2)).add (RatPolyCoeffEqv.refl _))).trans ?_
  refine (recurrence_finish (derivativePolynomial x n) (characterPolynomial x (n+1))
    (cap (Q'.ofNat (n+1)))).trans ?_
  exact (RatPolyCoeffEqv.refl _).add
    (((nat_cap_succ (n+1)).symm.mul_right (characterPolynomial x (n+1))).mul_left (cap 2))

private theorem chain_step (x a b u d : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (polyMul (cap 2) d) u)
        (polyMul (polyMul (cap 2) x) (polyMul b d)))
        (polyMul (cap (-1)) (polyMul a d)))
      (polyMul (derivativeStep x a b u) d) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.mul (.const 2) (.var 4)) (.var 3))
      (.mul (.mul (.const 2) (.var 0)) (.mul (.var 2) (.var 4))))
      (.mul (.const (-1)) (.mul (.var 1) (.var 4))))
    (.mul (.add (.mul (.const 2) (.var 3))
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.mul (.const (-1)) (.var 1)))) (.var 4))
    (by decide) (env x a b u d polyZero)

/-- Chain rule at coefficient equality, with the constructed positive
lower-character expansion. No rational evaluation or changed measure is used. -/
theorem angularDerivative_character_at (i j : Nat)
    (x : RatPoly) : ∀ n : Nat,
    RatPolyCoeffEqv (angularDerivative i j (characterPolynomial x n))
      (polyMul (derivativePolynomial x n) (angularDerivative i j x))
  | 0 => (angularDerivative_one i j).trans
        ((cap_mul_left 0 (angularDerivative i j x)).trans
          (RatPolyCoeffEqv.zero_smul _)).symm
  | 1 => (angularDerivative_smul i j 2 x).trans (cap_mul_left 2 _).symm
  | n+2 => by
      let d := angularDerivative i j x
      have hnext := angularDerivative_character_at i j x (n+1)
      have hprev := angularDerivative_character_at i j x n
      refine (angularDerivative_add i j
        (polyMul (polySmul 2 x) (characterPolynomial x (n+1)))
        (polySmul (-1) (characterPolynomial x n))).trans ?_
      refine ((angularDerivative_mul i j (polySmul 2 x) (characterPolynomial x (n+1))).add
        (angularDerivative_smul i j (-1) (characterPolynomial x n))).trans ?_
      refine ((((angularDerivative_smul i j 2 x).trans (cap_mul_left 2 d).symm).mul
        (RatPolyCoeffEqv.refl _)).add
          ((cap_mul_left 2 x).symm.mul hnext)).add
            ((hprev.smul (-1)).trans (cap_mul_left (-1) _).symm) |>.trans ?_
      exact (chain_step x (derivativePolynomial x n) (derivativePolynomial x (n+1))
        (characterPolynomial x (n+1)) d).trans ((derivative_recurrence x n).mul_right d)

/-- Head-coordinate specialization of the arbitrary-coordinate chain rule. -/
theorem angularDerivative_character {i j : Nat} (_hi : i < 4) (_hj : j < 4)
    (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (angularDerivative i j (characterPolynomial x n))
      (polyMul (derivativePolynomial x n) (angularDerivative i j x)) :=
  angularDerivative_character_at i j x n

/-- The positive parity recurrence, now pinned to the actual angular derivative. -/
theorem angularDerivative_character_step {i j : Nat} (hi : i < 4) (hj : j < 4)
    (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (angularDerivative i j (characterPolynomial x (n+2)))
      (polyAdd (angularDerivative i j (characterPolynomial x n))
        (polyMul (polyMul (cap 2)
          (polyMul (cap (Q'.ofNat (n+2))) (characterPolynomial x (n+1))))
          (angularDerivative i j x))) := by
  refine (angularDerivative_character hi hj x (n+2)).trans ?_
  rw [derivativePolynomial, polyMul_add_left_exact]
  exact (angularDerivative_character hi hj x n).symm.add (RatPolyCoeffEqv.refl _)

/-- Cubic two-sided Haar certificates for the positive derivative polynomial.
The bound is independent of the number of shared quaternion variables. -/
def derivativePolynomialInterval {blocks : Nat} {x : RatPoly}
    (X : SquareBound blocks x 1) : ∀ n : Nat,
    Interval blocks (derivativePolynomial x n) (cubicBudget n)
  | 0 => (Interval.constant blocks 0 (Q'.le_refl' _)).weaken (cubicBudget_nonnegative 0)
  | 1 => (Interval.constant blocks 2 (by decide)).weaken two_le_cubicBudget_one
  | n+2 => ((derivativePolynomialInterval X n).add
      ((Interval.constant blocks 2 (by decide)).mul
        ((Interval.constant blocks (Q'.ofNat (n+2)) (HeatKernelRGStep.zero_le_ofNat _)).mul
          (sharpCharacterInterval X (n+1))))).weaken (cubicBudget_step n)

/-- The exact chain rule turns the cubic certificate into a certificate for
the actual angular derivative. A bound for D x is still a separate input. -/
def angularDerivativeCharacterInterval {blocks i j : Nat} {x : RatPoly} {d : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d) (n : Nat) :
    Interval blocks (angularDerivative i j (characterPolynomial x n)) (cubicBudget n * d) :=
  Interval.ofCoeff (angularDerivative_supported hb hi hj (character_squareBound X n).support)
    (angularDerivative_character hi hj x n) ((derivativePolynomialInterval X n).mul DX)

/-- The same cubic character budget for rotations at any supported coordinates. -/
def angularDerivativeCharacterIntervalAt {blocks i j : Nat} {x : RatPoly} {d : Q'}
    (hi : i < 4 * blocks) (hj : j < 4 * blocks) (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d) (n : Nat) :
    Interval blocks (angularDerivative i j (characterPolynomial x n)) (cubicBudget n * d) :=
  Interval.ofCoeff (angularDerivative_supported_at hi hj (character_squareBound X n).support)
    (angularDerivative_character_at i j x n) ((derivativePolynomialInterval X n).mul DX)

/-- Derivative control against any original positive-certificate background;
shared variables are retained, and no independence is required. -/
theorem angularDerivative_character_weighted_bound {blocks i j : Nat} {x r : RatPoly} {d : Q'}
    (hb : 0 < blocks) (hi : i < 4) (hj : j < 4) (X : SquareBound blocks x 1)
    (DX : Interval blocks (angularDerivative i j x) d)
    (R : QuaternionHaarSquareCertificate.Certificate blocks r) (n : Nat) :
    Q'.abs (quaternionHaar blocks (polyMul r (angularDerivative i j (characterPolynomial x n)))) ≤
      (cubicBudget n * d) * quaternionHaar blocks r :=
  (angularDerivativeCharacterInterval hb hi hj X DX n).weighted_haar_bound R

end YMGap.Continuum.QuaternionHaarCharacterDerivative

#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.derivativePolynomial
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivative_character
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivative_character_at
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivative_character_step
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.derivativePolynomialInterval
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivativeCharacterInterval
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivativeCharacterIntervalAt
#print axioms YMGap.Continuum.QuaternionHaarCharacterDerivative.angularDerivative_character_weighted_bound
