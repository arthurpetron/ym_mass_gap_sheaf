/-
# Linear algebra of the six-direction quaternion angular Laplacian

Coefficient-level additivity and scalar linearity for the existing
six-direction angular Laplacian, together with its Haar-carrier action on a
finite sum. These are polynomial identities only; they supply no energy or
spectral estimate.
-/

import YMGap.Continuum.QuaternionHaarExposedFundamentalEnergy

namespace YMGap.Continuum.QuaternionHaarAngularLaplacianLinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local infix:50 " ≈ " => Q'.eqv

/-- Distributing a six-term plane sum over pointwise addition. -/
theorem six_add (a b : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyAdd (a i j) (b i j)))
      (polyAdd (six a) (six b)) := by
  unfold six
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

/-- A rational scalar may be moved outside the six-term plane sum. -/
theorem six_smul (c : Q') (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polySmul c (a i j)))
      (polySmul c (six a)) := by
  unfold six
  have h4 : RatPolyCoeffEqv
      (polyAdd (polySmul c (a 1 3)) (polySmul c (a 2 3)))
      (polySmul c (polyAdd (a 1 3) (a 2 3))) :=
    (RatPolyCoeffEqv.smul_add c (a 1 3) (a 2 3)).symm
  have h3 : RatPolyCoeffEqv
      (polyAdd (polySmul c (a 1 2))
        (polyAdd (polySmul c (a 1 3)) (polySmul c (a 2 3))))
      (polySmul c (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))) :=
    ((RatPolyCoeffEqv.refl _).add h4).trans
      (RatPolyCoeffEqv.smul_add c (a 1 2) (polyAdd (a 1 3) (a 2 3))).symm
  have h2 : RatPolyCoeffEqv
      (polyAdd (polySmul c (a 0 3))
        (polyAdd (polySmul c (a 1 2))
          (polyAdd (polySmul c (a 1 3)) (polySmul c (a 2 3)))))
      (polySmul c (polyAdd (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3))))) :=
    ((RatPolyCoeffEqv.refl _).add h3).trans
      (RatPolyCoeffEqv.smul_add c (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))).symm
  have h1 : RatPolyCoeffEqv
      (polyAdd (polySmul c (a 0 2))
        (polyAdd (polySmul c (a 0 3))
          (polyAdd (polySmul c (a 1 2))
            (polyAdd (polySmul c (a 1 3)) (polySmul c (a 2 3))))))
      (polySmul c (polyAdd (a 0 2) (polyAdd (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))))) :=
    ((RatPolyCoeffEqv.refl _).add h2).trans
      (RatPolyCoeffEqv.smul_add c (a 0 2)
        (polyAdd (a 0 3) (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3))))).symm
  exact ((RatPolyCoeffEqv.refl _).add h1).trans
    (RatPolyCoeffEqv.smul_add c (a 0 1)
      (polyAdd (a 0 2) (polyAdd (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))))).symm

/-- A common left polynomial factor may be moved outside the six-term sum. -/
theorem six_mul_left (f : RatPoly) (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (six (fun i j => polyMul f (a i j)))
      (polyMul f (six a)) := by
  unfold six
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 0) (.var 3))
          (.add (.mul (.var 0) (.var 4))
            (.add (.mul (.var 0) (.var 5)) (.mul (.var 0) (.var 6)))))))
    (.mul (.var 0) (.add (.var 1) (.add (.var 2) (.add (.var 3)
      (.add (.var 4) (.add (.var 5) (.var 6)))))))
    (by decide) (fun
      | 0 => f | 1 => a 0 1 | 2 => a 0 2 | 3 => a 0 3
      | 4 => a 1 2 | 5 => a 1 3 | _ => a 2 3)

private theorem secondAngular_add (i j : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polyAdd p q)))
      (polyAdd (angularDerivative i j (angularDerivative i j p))
        (angularDerivative i j (angularDerivative i j q))) :=
  (angularDerivative_congr i j (angularDerivative_add i j p q)).trans
    (angularDerivative_add i j (angularDerivative i j p)
      (angularDerivative i j q))

/-- The full six-direction Laplacian is coefficientwise additive. -/
theorem angularLaplacian_add (p q : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polyAdd p q))
      (polyAdd (angularLaplacian p) (angularLaplacian q)) := by
  unfold angularLaplacian
  exact ((secondAngular_add 0 1 p q).add
    ((secondAngular_add 0 2 p q).add
      ((secondAngular_add 0 3 p q).add
        ((secondAngular_add 1 2 p q).add
          ((secondAngular_add 1 3 p q).add (secondAngular_add 2 3 p q)))))).trans
    (six_add
      (fun i j => angularDerivative i j (angularDerivative i j p))
      (fun i j => angularDerivative i j (angularDerivative i j q)))

private theorem secondAngular_smul (i j : Nat) (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j (polySmul c p)))
      (polySmul c (angularDerivative i j (angularDerivative i j p))) :=
  (angularDerivative_congr i j (angularDerivative_smul i j c p)).trans
    (angularDerivative_smul i j c (angularDerivative i j p))

/-- The full six-direction Laplacian commutes coefficientwise with scalar
multiplication. -/
theorem angularLaplacian_smul (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (polySmul c p))
      (polySmul c (angularLaplacian p)) := by
  unfold angularLaplacian
  exact ((secondAngular_smul 0 1 c p).add
    ((secondAngular_smul 0 2 c p).add
      ((secondAngular_smul 0 3 c p).add
        ((secondAngular_smul 1 2 c p).add
          ((secondAngular_smul 1 3 c p).add (secondAngular_smul 2 3 c p)))))).trans
    (six_smul c (fun i j => angularDerivative i j (angularDerivative i j p)))

private theorem angularDerivative_zero_local (i j : Nat) :
    RatPolyCoeffEqv (angularDerivative i j polyZero) polyZero :=
  (angularDerivative_congr i j (RatPolyCoeffEqv.zero_smul polyOne).symm).trans
    ((angularDerivative_smul i j 0 polyOne).trans
      (RatPolyCoeffEqv.zero_smul _))

private theorem secondAngular_one (i j : Nat) :
    RatPolyCoeffEqv
      (angularDerivative i j (angularDerivative i j polyOne)) polyZero :=
  (angularDerivative_congr i j (angularDerivative_one i j)).trans
    (angularDerivative_zero_local i j)

/-- The angular Laplacian annihilates the constant polynomial one. -/
theorem angularLaplacian_one :
    RatPolyCoeffEqv (angularLaplacian polyOne) polyZero := by
  unfold angularLaplacian
  have h := ((secondAngular_one 0 1).add
    ((secondAngular_one 0 2).add
      ((secondAngular_one 0 3).add
        ((secondAngular_one 1 2).add
          ((secondAngular_one 1 3).add (secondAngular_one 2 3))))))
  change RatPolyCoeffEqv _ polyZero at h
  exact h

/-- The Laplacian distributes over the six-term plane sum. -/
theorem angularLaplacian_six (a : Nat → Nat → RatPoly) :
    RatPolyCoeffEqv (angularLaplacian (six a))
      (six (fun i j => angularLaplacian (a i j))) := by
  unfold six
  have h4 : RatPolyCoeffEqv
      (angularLaplacian (polyAdd (a 1 3) (a 2 3)))
      (polyAdd (angularLaplacian (a 1 3)) (angularLaplacian (a 2 3))) :=
    angularLaplacian_add _ _
  have h3 : RatPolyCoeffEqv
      (angularLaplacian (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3))))
      (polyAdd (angularLaplacian (a 1 2))
        (polyAdd (angularLaplacian (a 1 3)) (angularLaplacian (a 2 3)))) :=
    (angularLaplacian_add _ _).trans ((RatPolyCoeffEqv.refl _).add h4)
  have h2 : RatPolyCoeffEqv
      (angularLaplacian (polyAdd (a 0 3)
        (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3)))))
      (polyAdd (angularLaplacian (a 0 3))
        (polyAdd (angularLaplacian (a 1 2))
          (polyAdd (angularLaplacian (a 1 3)) (angularLaplacian (a 2 3))))) :=
    (angularLaplacian_add _ _).trans ((RatPolyCoeffEqv.refl _).add h3)
  have h1 : RatPolyCoeffEqv
      (angularLaplacian (polyAdd (a 0 2)
        (polyAdd (a 0 3)
          (polyAdd (a 1 2) (polyAdd (a 1 3) (a 2 3))))))
      (polyAdd (angularLaplacian (a 0 2))
        (polyAdd (angularLaplacian (a 0 3))
          (polyAdd (angularLaplacian (a 1 2))
            (polyAdd (angularLaplacian (a 1 3)) (angularLaplacian (a 2 3)))))) :=
    (angularLaplacian_add _ _).trans ((RatPolyCoeffEqv.refl _).add h2)
  exact (angularLaplacian_add _ _).trans ((RatPolyCoeffEqv.refl _).add h1)

/-- Pointwise original Haar-carrier equalities pass through the six-term sum. -/
theorem six_carrier {blocks : Nat} {a b : Nat → Nat → RatPoly}
    (h : ∀ i j, i < 4 → j < 4 → HaarCarrierEqv blocks (a i j) (b i j)) :
    HaarCarrierEqv blocks (six a) (six b) := by
  unfold six
  exact HaarCarrierEqv.add (h 0 1 (by decide) (by decide))
    (HaarCarrierEqv.add (h 0 2 (by decide) (by decide))
      (HaarCarrierEqv.add (h 0 3 (by decide) (by decide))
        (HaarCarrierEqv.add (h 1 2 (by decide) (by decide))
          (HaarCarrierEqv.add (h 1 3 (by decide) (by decide))
            (h 2 3 (by decide) (by decide))))))

#print axioms six_add
#print axioms six_smul
#print axioms six_mul_left
#print axioms angularLaplacian_add
#print axioms angularLaplacian_smul
#print axioms angularLaplacian_one
#print axioms angularLaplacian_six
#print axioms six_carrier

end YMGap.Continuum.QuaternionHaarAngularLaplacianLinear
