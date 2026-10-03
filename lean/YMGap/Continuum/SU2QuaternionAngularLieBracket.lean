/-
# Actual overlapping angular Lie bracket on the original Haar carrier

The coordinate rotations are the existing x_i partial_j-x_j partial_i.
Their overlapping-plane bracket is proved from their product rule, exact
mixed-partial commutation, and the original padded coordinate derivative
pins. All other blocks remain arbitrary shared spectators. Haar-carrier
equality, not false raw coefficient equality of padded constants, is used.
The relation survives subsequent angular derivatives by the existing
angularDerivative_carrier theorem. Casimir centrality, Gamma2 positivity,
and a conditional Poincare estimate are not asserted here.
-/

import YMGap.Continuum.SU2QuaternionDerivativeCommutation
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

namespace YMGap.Continuum.SU2QuaternionAngularLieBracket

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionDerivativeCommutation
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval

private def negativeField (i j : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (polyMul (polyVar i) (ratDerivative j p))
    (polyNeg (polyMul (polyVar j) (ratDerivative i p)))

private theorem field_negative (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j p) (negativeField i j p) :=
  (RatPolyCoeffEqv.refl _).add (neg_smul _).symm

private theorem coordinate_left {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar i)) (polyNeg (polyVar j)) := by
  have hz := ((ratDerivative_polyVar_ne j i (Ne.symm hij)).mul_left (polyVar i)).trans
    (RatPolyCoeffEqv.mul_zero_right _)
  exact (HaarCarrierEqv.add (RatPolyCoeffEqv.haarCarrier hz)
    (HaarCarrierEqv.smul (-1) (derivativeFactor_self_carrier blocks j i hb hj hi))).trans
    (RatPolyCoeffEqv.haarCarrier ((RatPolyCoeffEqv.zero_add _).trans (neg_smul _).symm))

private theorem coordinate_right {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar j)) (polyVar i) := by
  have hz := ((((ratDerivative_polyVar_ne i j hij).mul_left (polyVar j)).trans
    (RatPolyCoeffEqv.mul_zero_right _)).smul (-1)).trans (RatPolyCoeffEqv.smul_zero _)
  exact (HaarCarrierEqv.add (derivativeFactor_self_carrier blocks i j hb hi hj)
    (RatPolyCoeffEqv.haarCarrier hz)).trans
    (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.add_zero _))

private theorem coordinate_absent (i j k : Nat) (hki : k ≠ i) (hkj : k ≠ j) :
    RatPolyCoeffEqv (angularDerivative i j (polyVar k)) polyZero := by
  unfold angularDerivative
  have h := (((ratDerivative_polyVar_ne j k (Ne.symm hkj)).mul_left (polyVar i)).trans
    (RatPolyCoeffEqv.mul_zero_right _)).add
      (((((ratDerivative_polyVar_ne i k (Ne.symm hki)).mul_left (polyVar j)).trans
        (RatPolyCoeffEqv.mul_zero_right _)).smul (-1)).trans
        (RatPolyCoeffEqv.smul_zero _))
  exact h.trans (RatPolyCoeffEqv.zero_add _)

private theorem second_expansion (i j k l : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (angularDerivative k l p))
      (polyAdd
        (polyAdd (polyMul (angularDerivative i j (polyVar k)) (ratDerivative l p))
          (polyMul (polyVar k) (negativeField i j (ratDerivative l p))))
        (polyNeg
          (polyAdd (polyMul (angularDerivative i j (polyVar l)) (ratDerivative k p))
            (polyMul (polyVar l) (negativeField i j (ratDerivative k p)))))) := by
  have he := (angularDerivative_congr i j (field_negative k l p)).trans
    ((angularDerivative_add i j _ _).trans
      ((angularDerivative_mul i j _ _).add
        ((angularDerivative_neg i j _).trans
          (RatPolyCoeffEqv.neg (angularDerivative_mul i j _ _)))))
  exact he.trans
    (((RatPolyCoeffEqv.refl _).add
      ((field_negative i j _).mul_left (polyVar k))).add
      (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl _).add
        ((field_negative i j _).mul_left (polyVar l)))))

private def firstForm (i j k : Nat) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (polyVar i) (ratDerivative k p))
      (polyMul (polyVar j) (negativeField i j (ratDerivative k p))))
    (polyNeg (polyMul (polyVar k) (negativeField i j (ratDerivative j p))))

private def reverseForm (i j k : Nat) (p : RatPoly) : RatPoly :=
  polyAdd
    (polyMul (polyVar i)
      (polyAdd (polyMul (polyVar j) (ratDerivative j (ratDerivative k p)))
        (polyNeg (polyMul (polyVar k) (ratDerivative j (ratDerivative j p))))))
    (polyNeg
      (polyAdd (polyMul (polyNeg (polyVar k)) (ratDerivative i p))
        (polyMul (polyVar j)
          (polyAdd (polyMul (polyVar j) (ratDerivative i (ratDerivative k p)))
            (polyNeg (polyMul (polyVar k) (ratDerivative i (ratDerivative j p))))))))

/-- The actual SO(4) overlapping-plane bracket [D_ij,D_jk]=D_ik.
No support premise on p restricts its shared spectator dependence. -/
theorem overlapping_planes_bracket {blocks i j k : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hk : k < 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : RatPoly) :
    HaarCarrierEqv blocks
      (polyAdd (angularDerivative i j (angularDerivative j k p))
        (polyNeg (angularDerivative j k (angularDerivative i j p))))
      (angularDerivative i k p) := by
  have hzero1 := RatPolyCoeffEqv.haarCarrier (blocks := blocks)
    (((coordinate_absent i j k (Ne.symm hik) (Ne.symm hjk)).mul_right
      (ratDerivative j p)).trans (RatPolyCoeffEqv.mul_zero_left _))
  have hfirst : HaarCarrierEqv blocks
      (angularDerivative i j (angularDerivative j k p)) (firstForm i j k p) :=
    (RatPolyCoeffEqv.haarCarrier (second_expansion i j j k p)).trans
      ((HaarCarrierEqv.add
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul_right _ (coordinate_right hb hi hj hij))
          (HaarCarrierEqv.refl blocks _))
        (HaarCarrierEqv.neg
          ((HaarCarrierEqv.add hzero1 (HaarCarrierEqv.refl blocks _)).trans
            (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _))))))
  have hzero2 := RatPolyCoeffEqv.haarCarrier (blocks := blocks)
    (((coordinate_absent j k i hij hik).mul_right (ratDerivative j p)).trans
      (RatPolyCoeffEqv.mul_zero_left _))
  have hleft : HaarCarrierEqv blocks
      (negativeField j k (ratDerivative j p))
      (polyAdd (polyMul (polyVar j) (ratDerivative j (ratDerivative k p)))
        (polyNeg (polyMul (polyVar k) (ratDerivative j (ratDerivative j p))))) :=
    RatPolyCoeffEqv.haarCarrier
      (((ratDerivative_comm k j p).mul_left (polyVar j)).add (RatPolyCoeffEqv.refl _))
  have hright : HaarCarrierEqv blocks
      (negativeField j k (ratDerivative i p))
      (polyAdd (polyMul (polyVar j) (ratDerivative i (ratDerivative k p)))
        (polyNeg (polyMul (polyVar k) (ratDerivative i (ratDerivative j p))))) :=
    RatPolyCoeffEqv.haarCarrier
      (((ratDerivative_comm k i p).mul_left (polyVar j)).add
        (RatPolyCoeffEqv.neg ((ratDerivative_comm j i p).mul_left (polyVar k))))
  have hreverse : HaarCarrierEqv blocks
      (angularDerivative j k (angularDerivative i j p)) (reverseForm i j k p) :=
    (RatPolyCoeffEqv.haarCarrier (second_expansion j k i j p)).trans
      (HaarCarrierEqv.add
        ((HaarCarrierEqv.add hzero2 (HaarCarrierEqv.mul_left (polyVar i) hleft)).trans
          (RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.zero_add _)))
        (HaarCarrierEqv.neg (HaarCarrierEqv.add
          (HaarCarrierEqv.mul_right _ (coordinate_left hb hj hk hjk))
          (HaarCarrierEqv.mul_left (polyVar j) hright))))
  have hr : RatPolyCoeffEqv
      (polyAdd (firstForm i j k p) (polyNeg (reverseForm i j k p)))
      (negativeField i k p) := by
    let env : Nat → RatPoly := fun
      | 0 => polyVar i | 1 => polyVar j | 2 => polyVar k
      | 3 => ratDerivative i p | 4 => ratDerivative k p
      | 5 => ratDerivative j (ratDerivative k p)
      | 6 => ratDerivative i (ratDerivative k p)
      | 7 => ratDerivative j (ratDerivative j p)
      | _ => ratDerivative i (ratDerivative j p)
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add
        (.add (.add (.mul (.var 0) (.var 4))
          (.mul (.var 1) (.add (.mul (.var 0) (.var 5))
            (.neg (.mul (.var 1) (.var 6))))))
          (.neg (.mul (.var 2) (.add (.mul (.var 0) (.var 7))
            (.neg (.mul (.var 1) (.var 8)))))))
        (.neg (.add
          (.mul (.var 0) (.add (.mul (.var 1) (.var 5))
            (.neg (.mul (.var 2) (.var 7)))))
          (.neg (.add (.mul (.neg (.var 2)) (.var 3))
            (.mul (.var 1) (.add (.mul (.var 1) (.var 6))
              (.neg (.mul (.var 2) (.var 8))))))))))
      (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 2) (.var 3))))
      (by decide) env
  exact ((HaarCarrierEqv.add hfirst (HaarCarrierEqv.neg hreverse)).trans
    (RatPolyCoeffEqv.haarCarrier hr)).trans
      (RatPolyCoeffEqv.haarCarrier (field_negative i k p)).symm

/-- Reversing the ordered coordinate plane reverses the actual field. -/
theorem angular_plane_antisymmetry (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative j i p) (polyNeg (angularDerivative i j p)) := by
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.var 1) (.neg (.var 0)))
    (.neg (.add (.var 0) (.neg (.var 1)))) (by decide)
    (fun | 0 => polyMul (polyVar i) (ratDerivative j p)
         | _ => polyMul (polyVar j) (ratDerivative i p))
  exact ((field_negative j i p).trans hr).trans
    (RatPolyCoeffEqv.neg (field_negative i j p)).symm

private theorem absent_expansion (i j k l : Nat)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (angularDerivative k l p))
      (polyAdd (polyMul (polyVar k) (negativeField i j (ratDerivative l p)))
        (polyNeg (polyMul (polyVar l) (negativeField i j (ratDerivative k p))))) := by
  have hzero1 := ((coordinate_absent i j k (Ne.symm hik) (Ne.symm hjk)).mul_right
    (ratDerivative l p)).trans (RatPolyCoeffEqv.mul_zero_left _)
  have hzero2 := ((coordinate_absent i j l (Ne.symm hil) (Ne.symm hjl)).mul_right
    (ratDerivative k p)).trans (RatPolyCoeffEqv.mul_zero_left _)
  exact (second_expansion i j k l p).trans
    (((hzero1.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)).add
      (RatPolyCoeffEqv.neg
        ((hzero2.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _))))

/-- Disjoint coordinate planes commute at coefficient strength, for arbitrary
coordinate indices and all signed inputs. No spectator is integrated away. -/
theorem disjoint_planes_commute (i j k l : Nat)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j (angularDerivative k l p))
      (angularDerivative k l (angularDerivative i j p)) := by
  have hjets1 : RatPolyCoeffEqv (negativeField k l (ratDerivative j p))
      (polyAdd (polyMul (polyVar k) (ratDerivative j (ratDerivative l p)))
        (polyNeg (polyMul (polyVar l) (ratDerivative j (ratDerivative k p))))) :=
    ((ratDerivative_comm l j p).mul_left (polyVar k)).add
      (RatPolyCoeffEqv.neg ((ratDerivative_comm k j p).mul_left (polyVar l)))
  have hjets2 : RatPolyCoeffEqv (negativeField k l (ratDerivative i p))
      (polyAdd (polyMul (polyVar k) (ratDerivative i (ratDerivative l p)))
        (polyNeg (polyMul (polyVar l) (ratDerivative i (ratDerivative k p))))) :=
    ((ratDerivative_comm l i p).mul_left (polyVar k)).add
      (RatPolyCoeffEqv.neg ((ratDerivative_comm k i p).mul_left (polyVar l)))
  have hreverse := (absent_expansion k l i j (Ne.symm hik) (Ne.symm hjk)
    (Ne.symm hil) (Ne.symm hjl) p).trans
      ((hjets1.mul_left (polyVar i)).add
        (RatPolyCoeffEqv.neg (hjets2.mul_left (polyVar j))))
  have hr := coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 4))
      (.neg (.mul (.var 1) (.var 5)))))
      (.neg (.mul (.var 3) (.add (.mul (.var 0) (.var 6))
        (.neg (.mul (.var 1) (.var 7)))))))
    (.add (.mul (.var 0) (.add (.mul (.var 2) (.var 4))
      (.neg (.mul (.var 3) (.var 6)))))
      (.neg (.mul (.var 1) (.add (.mul (.var 2) (.var 5))
        (.neg (.mul (.var 3) (.var 7)))))))
    (by decide) (fun
      | 0 => polyVar i | 1 => polyVar j | 2 => polyVar k | 3 => polyVar l
      | 4 => ratDerivative j (ratDerivative l p)
      | 5 => ratDerivative i (ratDerivative l p)
      | 6 => ratDerivative j (ratDerivative k p)
      | _ => ratDerivative i (ratDerivative k p))
  exact ((absent_expansion i j k l hik hil hjk hjl p).trans hr).trans hreverse.symm

end YMGap.Continuum.SU2QuaternionAngularLieBracket

#print axioms YMGap.Continuum.SU2QuaternionAngularLieBracket.overlapping_planes_bracket
#print axioms YMGap.Continuum.SU2QuaternionAngularLieBracket.angular_plane_antisymmetry
#print axioms YMGap.Continuum.SU2QuaternionAngularLieBracket.disjoint_planes_commute
