/-
# Rational centering on the SAME intrinsic Wilson carrier

Subtract a rational multiple of the actual unit, using the literal dense
operations. Bilinearity and unit normalization compute the mixed form and
give the exact coefficient-square distance. These identities construct a
centered Cauchy stream without requiring completed real scalar operations.
The original small-nome guards, base and fixed-spacing scope are unchanged.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

def centerApprox {base : Nat} (x : IntrinsicExpression base) (q : Q') :
    IntrinsicExpression base := difference x (smul q (unit base))

private theorem sub_congr {a b c d : CReal} (ha : Equiv a b) (hc : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add ha (neg_congr hc)

private def centerValue (A B C : CReal) (q r : Q') : CReal :=
  sub (sub A (mul (ofQ' q) B)) (sub (mul (ofQ' r) C) (ofQ' (q*r)))

private theorem centerValue_expand (A B C : CReal) (q r : Q') :
    Equiv (sub (sub A (mul (ofQ' r) C)) (mul (ofQ' q) (sub B (ofQ' r))))
      (centerValue A B C q r) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.mul (.var 4) (.var 2))))
      (.neg (.mul (.var 3) (.add (.var 1) (.neg (.var 4))))))
    (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 1))))
      (.neg (.add (.mul (.var 4) (.var 2)) (.neg (.mul (.var 3) (.var 4))))))
    (by decide) (fun
      | 0 => A.approx n
      | 1 => B.approx n
      | 2 => C.approx n
      | 3 => q
      | _ => r)

private theorem centerValue_distance (A B C : CReal) (q r : Q') :
    Equiv
      (sub (sub (centerValue A B C q q) (centerValue A B C q r))
        (sub (centerValue A B C r q) (centerValue A B C r r)))
      (ofQ' ((q + -r)^2)) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  let F (a b : Nat) : RingNormaliser.PolyExpr :=
    .add (.add (.var 2) (.neg (.mul (.var a) (.var 3))))
      (.neg (.add (.mul (.var b) (.var 4)) (.neg (.mul (.var a) (.var b)))))
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (F 0 0) (.neg (F 0 1))) (.neg (.add (F 1 0) (.neg (F 1 1)))))
    (.mul (.add (.var 0) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.const 1)))
    (by decide) (fun
      | 0 => q
      | 1 => r
      | 2 => A.approx n
      | 3 => B.approx n
      | _ => C.approx n)

attribute [local irreducible] intrinsicForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "P" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "u" => unit base

theorem centerApprox_pairing_left (x y : IntrinsicExpression base) (q : Q') :
    Equiv (P (centerApprox x q) y) (sub (P x y) (mul (ofQ' q) (P u y))) :=
  (intrinsicForm_difference_left hw0 hw1 hsmall hd hs hb x (smul q u) y).trans
    (sub_congr (Equiv.refl _) (intrinsicForm_smul_left hw0 hw1 hsmall hd hs hb q u y))

theorem centerApprox_pairing_right (x y : IntrinsicExpression base) (r : Q') :
    Equiv (P x (centerApprox y r)) (sub (P x y) (mul (ofQ' r) (P x u))) :=
  (intrinsicForm_difference_right hw0 hw1 hsmall hd hs hb x y (smul r u)).trans
    (sub_congr (Equiv.refl _) (intrinsicForm_smul_right hw0 hw1 hsmall hd hs hb r x u))

/-- The residual unit coefficient is the actual scalar mean error. -/
theorem centerApprox_unit (x : IntrinsicExpression base) (q : Q') :
    Equiv (P (centerApprox x q) u) (sub (P x u) (ofQ' q)) :=
  (centerApprox_pairing_left hw0 hw1 hsmall hd hs hb x u q).trans
    (sub_congr (Equiv.refl _)
      ((TrigSignedAdd.mul_congr_right (intrinsicForm_unit_unit hw0 hw1 hsmall hd hs hb)).trans
        (CRealAlg.cmul_cone (ofQ' q))))

/-- Both original operands and both signed coefficients remain in the form. -/
theorem centerApprox_pairing (x y : IntrinsicExpression base) (q r : Q') :
    Equiv (P (centerApprox x q) (centerApprox y r))
      (sub (sub (P x y) (mul (ofQ' q) (P u y)))
        (sub (mul (ofQ' r) (P x u)) (ofQ' (q*r)))) := by
  have huy : Equiv (P u (centerApprox y r)) (sub (P u y) (ofQ' r)) :=
    (centerApprox_pairing_right hw0 hw1 hsmall hd hs hb u y r).trans
      (sub_congr (Equiv.refl _)
        ((TrigSignedAdd.mul_congr_right (intrinsicForm_unit_unit hw0 hw1 hsmall hd hs hb)).trans
          (CRealAlg.cmul_cone (ofQ' r))))
  exact (centerApprox_pairing_left hw0 hw1 hsmall hd hs hb x (centerApprox y r) q).trans
    ((sub_congr (centerApprox_pairing_right hw0 hw1 hsmall hd hs hb x y r)
      (TrigSignedAdd.mul_congr_right huy)).trans
      (centerValue_expand (P x y) (P u y) (P x u) q r))

/-- The exact squared distance supplies the constructive stream modulus. -/
theorem centerApprox_distance (x : IntrinsicExpression base) (q r : Q') :
    Equiv (distSq hw0 hw1 hsmall hd hs hb (centerApprox x q) (centerApprox x r))
      (ofQ' ((q + -r)^2)) := by
  have hexpand := intrinsicForm_difference_diagonal hw0 hw1 hsmall hd hs hb
    (centerApprox x q) (centerApprox x r)
  have hfour := sub_congr
    (sub_congr (centerApprox_pairing hw0 hw1 hsmall hd hs hb x x q q)
      (centerApprox_pairing hw0 hw1 hsmall hd hs hb x x q r))
    (sub_congr (centerApprox_pairing hw0 hw1 hsmall hd hs hb x x r q)
      (centerApprox_pairing hw0 hw1 hsmall hd hs hb x x r r))
  exact hexpand.trans (hfour.trans (centerValue_distance (P x x) (P u x) (P x u) q r))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox_pairing_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox_pairing_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra.centerApprox_distance
