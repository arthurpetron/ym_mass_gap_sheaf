/-
# Conserved Chebyshev energy on the original polynomial carrier

The exact identity U_n^2 + U_(n+1)^2 - 2*x*U_n*U_(n+1) = 1
gives a sum-of-squares bound for x*U_(n+1)-U_n. All equalities are
coefficient equalities on the existing character polynomials. A square
bound for x is the only input; no trigonometric representation is used.
-/

import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.QuaternionHaarChebyshevEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound

private def sq (e : PolyExpr) : PolyExpr := .mul e e
private def sub (a b : PolyExpr) : PolyExpr := .add a (.neg b)
private def energyExpr (x a b : PolyExpr) : PolyExpr :=
  sub (.add (sq a) (sq b)) (.mul (.mul (.const 2) x) (.mul a b))
private def stepExpr (x a b : PolyExpr) : PolyExpr :=
  .add (.mul (.mul (.const 2) x) b) (.mul (.const (-1)) a)
private def env3 (x a b : RatPoly) : Nat → RatPoly
  | 0 => x | 1 => a | _ => b

def energy (x a b : RatPoly) : RatPoly :=
  coeffEvalExpr (env3 x a b) (energyExpr (.var 0) (.var 1) (.var 2))

def step (x a b : RatPoly) : RatPoly :=
  coeffEvalExpr (env3 x a b) (stepExpr (.var 0) (.var 1) (.var 2))

theorem character_step_pin (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (characterPolynomial x (n+2))
      (step x (characterPolynomial x n) (characterPolynomial x (n+1))) :=
  (((cap_mul_left 2 x).symm).mul (RatPolyCoeffEqv.refl _)).add
    (cap_mul_left (-1) (characterPolynomial x n)).symm

theorem energy_congr {x a b c d : RatPoly} (ha : RatPolyCoeffEqv a c)
    (hb : RatPolyCoeffEqv b d) : RatPolyCoeffEqv (energy x a b) (energy x c d) :=
  ((ha.mul ha).add (hb.mul hb)).add
    (RatPolyCoeffEqv.neg ((RatPolyCoeffEqv.refl _).mul (ha.mul hb)))

theorem energy_step (x a b : RatPoly) :
    RatPolyCoeffEqv (energy x b (step x a b)) (energy x a b) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (energyExpr (.var 0) (.var 2) (stepExpr (.var 0) (.var 1) (.var 2)))
    (energyExpr (.var 0) (.var 1) (.var 2)) (by decide) (env3 x a b)

/-- Exact polynomial identity, at every spin. -/
theorem character_energy (x : RatPoly) : ∀ n : Nat,
    RatPolyCoeffEqv (energy x (characterPolynomial x n) (characterPolynomial x (n+1))) polyOne
  | 0 => by
    refine (energy_congr (RatPolyCoeffEqv.one_smul polyOne).symm
      (cap_mul_left 2 x).symm).trans ?_
    exact (coeffEvalExpr_eqv_of_normalize_eq
      (energyExpr (.var 0) (.const 1) (.mul (.const 2) (.var 0)))
      (.const 1) (by decide) (fun _ => x)).trans (RatPolyCoeffEqv.one_smul polyOne)
  | n+1 =>
    (energy_congr (RatPolyCoeffEqv.refl _) (character_step_pin x n)).trans
      ((energy_step x (characterPolynomial x n) (characterPolynomial x (n+1))).trans
        (character_energy x n))

/-- The cosine polynomial T_(n+2), expressed in the ORIGINAL characters. -/
def cosineNext (x : RatPoly) (n : Nat) : RatPoly :=
  polyAdd (polyMul x (characterPolynomial x (n+1))) (polyNeg (characterPolynomial x n))

theorem cosine_norm (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv
      (polyAdd (polyMul (cosineNext x n) (cosineNext x n))
        (polyMul (polyMul (characterPolynomial x (n+1)) (characterPolynomial x (n+1))) (gap 1 x)))
      polyOne :=
  (coeffEvalExpr_eqv_of_normalize_eq
    (.add (sq (sub (.mul (.var 0) (.var 2)) (.var 1)))
      (.mul (sq (.var 2)) (sub (.const 1) (sq (.var 0)))))
    (energyExpr (.var 0) (.var 1) (.var 2)) (by decide)
    (env3 x (characterPolynomial x n) (characterPolynomial x (n+1)))).trans (character_energy x n)

theorem cosine_gap (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (gap 1 (cosineNext x n))
      (polyMul (polyMul (characterPolynomial x (n+1)) (characterPolynomial x (n+1))) (gap 1 x)) :=
  (((RatPolyCoeffEqv.one_smul polyOne).trans (cosine_norm x n).symm).add
    (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (sub (.add (sq (.var 0)) (.var 1)) (sq (.var 0))) (.var 1) (by decide)
      (fun i => if i = 0 then cosineNext x n else
        polyMul (polyMul (characterPolynomial x (n+1)) (characterPolynomial x (n+1))) (gap 1 x)))

/-- Positive certificate for 1-T_(n+2)^2 with all shared variables retained. -/
def cosine_squareBound {blocks : Nat} {x : RatPoly} (X : SquareBound blocks x 1) (n : Nat) :
    SquareBound blocks (cosineNext x n) 1 where
  support := supported_add
    (supported_polyMul X.support (character_squareBound X (n+1)).support)
    (character_squareBound X n).neg.support
  nonnegative := Q'.zero_le_one
  certificate := .ofCoeff (cosine_gap x n)
    (Certificate.multiplySquare _ (character_squareBound X (n+1)).support X.certificate)

theorem character_cosine_step (x : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (characterPolynomial x (n+2))
      (polyAdd (characterPolynomial x n) (polySmul 2 (cosineNext x n))) :=
  (character_step_pin x n).trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (stepExpr (.var 0) (.var 1) (.var 2))
      (.add (.var 1) (.mul (.const 2) (sub (.mul (.var 0) (.var 2)) (.var 1))))
      (by decide) (env3 x (characterPolynomial x n) (characterPolynomial x (n+1)))).trans
      ((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 (cosineNext x n))))

end YMGap.Continuum.QuaternionHaarChebyshevEnergy

#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.character_step_pin
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.energy_congr
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.energy_step
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.character_energy
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.cosineNext
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.cosine_norm
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.cosine_gap
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.cosine_squareBound
#print axioms YMGap.Continuum.QuaternionHaarChebyshevEnergy.character_cosine_step
