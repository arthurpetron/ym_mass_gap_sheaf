/-
# The angular Casimir on every homogeneous harmonic quaternion polynomial

The six plane rotations are expanded on the original Haar carrier. Their
sum is radius times the Euclidean Laplacian, minus the second Euler sum,
minus three times the Euler field. Homogeneity and harmonicity therefore
give the exact eigenvalue `-n(n+2)` at every degree. No heat semigroup,
interacting energy comparison, or spectral gap is assumed or concluded.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy
import YMGap.Continuum.SU2QuaternionHeadDerivativeEuler

namespace YMGap.Continuum.QuaternionHaarAngularCasimir

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarAngularCarrier
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.SU2QuaternionHeadDerivativeEuler

local infix:50 " ≈ " => Q'.eqv

private theorem angular_as_neg (i j : Nat) (p : RatPoly) :
    RatPolyCoeffEqv (angularDerivative i j p)
      (polyAdd (polyMul (polyVar i) (ratDerivative j p))
        (polyNeg (polyMul (polyVar j) (ratDerivative i p)))) :=
  (RatPolyCoeffEqv.refl _).add (neg_smul _).symm

private theorem coordinate_left {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    HaarCarrierEqv blocks (angularDerivative i j (polyVar i))
      (polyNeg (polyVar j)) := by
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

private def plane (p : RatPoly) (i j : Nat) : RatPoly :=
  polyAdd
    (polyAdd (polyMul (polyNeg (polyVar j)) (ratDerivative j p))
      (polyMul (polyVar i)
        (polyAdd (polyMul (polyVar i) (ratDerivative j (ratDerivative j p)))
          (polyNeg (polyMul (polyVar j) (ratDerivative i (ratDerivative j p)))))))
    (polyNeg (polyAdd (polyMul (polyVar i) (ratDerivative i p))
      (polyMul (polyVar j)
        (polyAdd (polyMul (polyVar i) (ratDerivative j (ratDerivative i p)))
          (polyNeg (polyMul (polyVar j) (ratDerivative i (ratDerivative i p))))))))

private theorem second_plane {blocks i j : Nat} (hb : 0 < blocks)
    (hi : i < 4) (hj : j < 4) (hij : i ≠ j) (p : RatPoly) :
    HaarCarrierEqv blocks (angularDerivative i j (angularDerivative i j p))
      (plane p i j) := by
  have he := (angularDerivative_congr i j (angular_as_neg i j p)).trans
    ((angularDerivative_add i j _ _).trans
      ((angularDerivative_mul i j _ _).add
        ((angularDerivative_neg i j _).trans (RatPolyCoeffEqv.neg (angularDerivative_mul i j _ _)))))
  exact (RatPolyCoeffEqv.haarCarrier he).trans
    (HaarCarrierEqv.add
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul_right (ratDerivative j p) (coordinate_left hb hi hj hij))
        (HaarCarrierEqv.mul_left (polyVar i) (RatPolyCoeffEqv.haarCarrier (angular_as_neg i j (ratDerivative j p)))))
      (HaarCarrierEqv.neg (HaarCarrierEqv.add
        (HaarCarrierEqv.mul_right (ratDerivative i p) (coordinate_right hb hi hj hij))
        (HaarCarrierEqv.mul_left (polyVar j) (RatPolyCoeffEqv.haarCarrier (angular_as_neg i j (ratDerivative i p)))))))

private def fourExpr (f : Nat → PolyExpr) : PolyExpr :=
  .add (f 0) (.add (f 1) (.add (f 2) (f 3)))

private def sixExpr (f : Nat → Nat → PolyExpr) : PolyExpr :=
  .add (f 0 1) (.add (f 0 2) (.add (f 0 3)
    (.add (f 1 2) (.add (f 1 3) (f 2 3)))))

private def d (i : Nat) : PolyExpr := .var (4+i)
private def dd (i j : Nat) : PolyExpr := .var (8+4*i+j)

private def planeExpr (i j : Nat) : PolyExpr :=
  .add
    (.add (.mul (.neg (.var j)) (d j))
      (.mul (.var i) (.add (.mul (.var i) (dd j j)) (.neg (.mul (.var j) (dd i j))))))
    (.neg (.add (.mul (.var i) (d i))
      (.mul (.var j) (.add (.mul (.var i) (dd j i)) (.neg (.mul (.var j) (dd i i)))))))

private def env (p : RatPoly) (k : Nat) : RatPoly :=
  if k < 4 then polyVar k
  else if k < 8 then ratDerivative (k-4) p
  else ratDerivative ((k-8)/4) (ratDerivative ((k-8)%4) p)

/-- The Euclidean squared radius, with its four coordinates explicit. -/
def radius : RatPoly := polyFour
  (polyMul (polyVar 0) (polyVar 0)) (polyMul (polyVar 1) (polyVar 1))
  (polyMul (polyVar 2) (polyVar 2)) (polyMul (polyVar 3) (polyVar 3))

private theorem collect_planes (p : RatPoly) :
    RatPolyCoeffEqv (six (plane p))
      (polyAdd (polyMul radius (headLaplacian p))
        (polyAdd (polyNeg (secondEulerSum p)) (polySmul (-3) (headEuler p)))) := by
  have hc := coeffEvalExpr_eqv_of_normalize_eq
    (sixExpr planeExpr)
    (.add (.mul (fourExpr (fun i => .mul (.var i) (.var i)))
        (fourExpr (fun i => dd i i)))
      (.add (.neg (fourExpr (fun i => .mul (.var i)
          (fourExpr (fun j => .mul (.var j) (dd j i))))))
        (.mul (.const (-3)) (fourExpr (fun i => .mul (.var i) (d i))))))
    (by decide +kernel) (env p)
  exact hc.trans ((RatPolyCoeffEqv.refl _).add
    ((RatPolyCoeffEqv.refl _).add (cap_mul_left (-3) (headEuler p))))

/-- The full angular-versus-Euclidean differential identity. Both orders of
each mixed partial are retained, so no derivative commutation is assumed. -/
theorem angularLaplacian_euler {blocks : Nat} (hb : 0 < blocks) (p : RatPoly) :
    HaarCarrierEqv blocks (angularLaplacian p)
      (polyAdd (polyMul radius (headLaplacian p))
        (polyAdd (polyNeg (secondEulerSum p)) (polySmul (-3) (headEuler p)))) := by
  have h (i j : Nat) (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :=
    second_plane hb hi hj hij p
  exact (HaarCarrierEqv.add (h 0 1 (by decide) (by decide) (by decide))
    (HaarCarrierEqv.add (h 0 2 (by decide) (by decide) (by decide))
      (HaarCarrierEqv.add (h 0 3 (by decide) (by decide) (by decide))
        (HaarCarrierEqv.add (h 1 2 (by decide) (by decide) (by decide))
          (HaarCarrierEqv.add (h 1 3 (by decide) (by decide) (by decide))
            (h 2 3 (by decide) (by decide) (by decide))))))).trans
    (RatPolyCoeffEqv.haarCarrier (collect_planes p))

private theorem casimir_scalar (n : Nat) :
    -(Q'.ofNat (n-1) * Q'.ofNat n) + (-3) * Q'.ofNat n ≈
      -(Q'.ofNat n * (Q'.ofNat n + 2)) := by
  cases n with
  | zero => decide
  | succ n =>
    simp only [Nat.add_sub_cancel]
    have hn := Q'.ofNat_add_eqv n 1
    have hs : Q'.ofNat (n+1) ≈ Q'.ofNat n + 1 :=
      Q'.eqv_trans _ _ _ hn (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide))
    have hm : -(Q'.ofNat n * (Q'.ofNat n + 1)) + (-3) * (Q'.ofNat n + 1) ≈
        -((Q'.ofNat n + 1) * ((Q'.ofNat n + 1) + 2)) :=
      poly_identity_of_normal_eq
        (.add (.neg (.mul (.var 0) (.add (.var 0) (.const 1))))
          (.mul (.const (-3)) (.add (.var 0) (.const 1))))
        (.neg (.mul (.add (.var 0) (.const 1))
          (.add (.add (.var 0) (.const 1)) (.const 2))))
        (by decide) (fun _ => Q'.ofNat n)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ hs))
        (Q'.mul_eqv_congr_left _ _ _ hs))
      (Q'.eqv_trans _ _ _ hm
        (Q'.eqv_symm (Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hs)
            (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hs (Q'.eqv_refl 2)))))))

/-- All-degree angular Casimir on the same quaternion Haar carrier. -/
theorem harmonic_angularLaplacian {blocks n : Nat} (hb : 0 < blocks)
    (p : RatPoly) (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    HaarCarrierEqv blocks (angularLaplacian p)
      (polySmul (-(Q'.ofNat n * (Q'.ofNat n + 2))) p) := by
  have hz := (hh.mul_left radius).trans (RatPolyCoeffEqv.mul_zero_right _)
  have he := headEuler_of_blockDegree n p hp
  have hsecond := secondEulerSum_of_blockDegree hp
  have hneg := (RatPolyCoeffEqv.neg hsecond).trans (neg_smul _)
  have hc := (hneg.trans (RatPolyCoeffEqv.smul_assoc _ _ p)).add
    ((he.smul (-3)).trans (RatPolyCoeffEqv.smul_assoc _ _ p))
  have hscalar : (-1) * (Q'.ofNat (n-1) * Q'.ofNat n) + (-3) * Q'.ofNat n ≈
      -(Q'.ofNat n * (Q'.ofNat n + 2)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
          (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))
        (Q'.eqv_refl _)) (casimir_scalar n)
  exact (angularLaplacian_euler hb p).trans
    (RatPolyCoeffEqv.haarCarrier ((hz.add hc).trans
      ((RatPolyCoeffEqv.zero_add _).trans
        ((RatPolyCoeffEqv.add_smul_same _ _ p).trans
          (RatPolyCoeffEqv.smul_coefficient hscalar p)))))

end YMGap.Continuum.QuaternionHaarAngularCasimir

#print axioms YMGap.Continuum.QuaternionHaarAngularCasimir.angularLaplacian_euler
#print axioms YMGap.Continuum.QuaternionHaarAngularCasimir.harmonic_angularLaplacian
