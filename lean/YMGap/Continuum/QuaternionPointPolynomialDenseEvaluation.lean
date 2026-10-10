/-
Exact evaluation at the rational points of the ACTUAL completed quaternion
carrier. The completed Point is the existing Cauchy-row quotient; no real
representative is selected from it. This is a polynomial evaluation pin,
not a continuous Haar integral or a completed-function approximation.
-/

import YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
import YMGap.Continuum.QuaternionHaarTensorBernsteinRepair

namespace YMGap.Continuum.QuaternionPointPolynomialDenseEvaluation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPointPolynomialHaarTranslation
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.RepTheory
open YMGap.RepTheory.RationalQuaternion
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionCauchyGroup
open YMGap.RepTheory.RationalQuaternionCoordinateCompletion

local infix:50 " ≈ " => Q'.eqv

/-- A constant rational quaternion row has its original rational coordinate
as every approximation. This pins the quotient coordinate without choosing
any representative of an arbitrary completed point. -/
theorem pointCoordinate_embed (q : UnitNorm) (i : Fin 4) :
    pointCoordinate i (embed q) = rational (coordinate q.val i) := by
  change Quotient.mk crealSetoid (rowCoordinate (chordSeminorm.constant q) i) =
    Quotient.mk crealSetoid (CReal.ofQ' (coordinate q.val i))
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_refl _

/-- The polynomial environment of a dense rational point is precisely the
rational embedding of the same four raw quaternion coordinates, then zero. -/
theorem pointEnvironment_embed (q : UnitNorm) (j : Nat) :
    pointEnvironment (embed q) j = rational (environmentOf q.val j) := by
  match j with
  | 0 => exact pointCoordinate_embed q ⟨0, by decide⟩
  | 1 => exact pointCoordinate_embed q ⟨1, by decide⟩
  | 2 => exact pointCoordinate_embed q ⟨2, by decide⟩
  | 3 => exact pointCoordinate_embed q ⟨3, by decide⟩
  | k+4 =>
      have hk : ¬ k+4 < 4 := by omega
      simp [pointEnvironment, environmentOf, hk]

private theorem rational_add (a b : Q') :
    RCadd (rational a) (rational b) = rational (a+b) := by
  unfold rational
  rw [RCadd_mk]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem rational_mul (a b : Q') :
    RCmul (rational a) (rational b) = rational (a*b) := by
  unfold rational
  rw [RCmul_mk]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem rcPower_rational (a : Q') : ∀ e : Nat,
    rcPower (rational a) e = rational (qpow a e)
  | 0 => rfl
  | e+1 => by
      change RCmul (rcPower (rational a) e) (rational a) =
        rational (qpow a e * a)
      rw [rcPower_rational a e, rational_mul]

private theorem rcMonomial_rational (rho : Nat → Q') :
    ∀ (i : Nat) (m : List Nat),
      rcMonomialFrom (fun j => rational (rho j)) i m =
        rational (evalMonoFrom rho i m)
  | _, [] => rfl
  | i, e::m => by
      change RCmul (rcPower (rational (rho i)) e)
        (rcMonomialFrom (fun j => rational (rho j)) (i+1) m) = _
      rw [rcPower_rational, rcMonomial_rational rho (i+1) m, rational_mul]
      rfl

private theorem evalRC_rational (rho : Nat → Q') : ∀ p : RatPoly,
    evalRC (fun j => rational (rho j)) p = rational (evalRatPoly rho p)
  | [] => rfl
  | t::p => by
      change RCadd (RCmul (rational t.2)
        (rcMonomialFrom (fun j => rational (rho j)) 0 t.1))
        (evalRC (fun j => rational (rho j)) p) = _
      rw [rcMonomial_rational rho 0 t.1, evalRC_rational rho p,
        rational_mul, rational_add]
      rfl

/-- Actual finite RatPoly evaluation at the dense embedding is the rational
image of its original raw evaluation. No Haar-carrier relation is used. -/
theorem pointEval_embed (q : UnitNorm) (p : RatPoly) :
    pointEval (embed q) p =
      rational (evalRatPoly (environmentOf q.val) p) := by
  unfold pointEval
  have henv : pointEnvironment (embed q) =
      fun j => rational (environmentOf q.val j) :=
    funext (pointEnvironment_embed q)
  rw [henv]
  exact evalRC_rational (environmentOf q.val) p

#print axioms pointCoordinate_embed
#print axioms pointEnvironment_embed
#print axioms pointEval_embed

end YMGap.Continuum.QuaternionPointPolynomialDenseEvaluation
