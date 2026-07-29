/-
# Exact compact-cube bounds for the coupled BF4 action

The geometric BF4 endpoint kernel is evaluated on ten unit quaternions, hence
on forty coordinates of absolute value at most one.  This file proves the
corresponding polynomial estimate constructively:

  `0 ≤ A(source,target) ≤ ‖A‖₁ = 133/4`.

The lower bound is the already-certified LDL positivity of the genuine
three-colour `(K,S)` action.  The upper bound is a direct finite-polynomial
argument, not a numerical estimate: every compact-cube monomial has absolute
value at most one, so the value is bounded by the exact coefficient `L¹`
norm.  The deliberately coarse cube ceiling is enough for the exponential
shift used by the partition-positivity layer.

No classical reasoning, approximation, or new analytic input is used.
-/

import YMGap.Continuum.BF4GeometricHaarMehlerProjection

namespace YMGap.Continuum.BF4CompactCoupledActionBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection

local infix:50 " ≈ " => Q'.eqv

/-- A rational environment in the coordinate cube `[-1,1]^ℕ`.  Only the
finite prefix used by a polynomial matters. -/
def CompactCubeEnvironment (rho : Nat → Q') : Prop :=
  ∀ index, Q'.abs (rho index) ≤ (1 : Q')

private theorem qpow_abs_le_one {x : Q'}
    (hx : Q'.abs x ≤ (1 : Q')) :
    ∀ exponent : Nat,
      Q'.abs (qpow x exponent) ≤ (1 : Q')
  | 0 => by
      change Q'.abs (1 : Q') ≤ (1 : Q')
      decide
  | exponent + 1 => by
      rw [qpow_succ]
      exact Q'.le_trans' _ _ _
        (ExpNeg.abs_mul_le (qpow x exponent) x)
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg
            (qpow_abs_le_one hx exponent) hx
            Q'.zero_le_one (Q'.abs_nonneg _))
          (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

private theorem evalMonoFrom_abs_le_one
    (rho : Nat → Q') (hrho : CompactCubeEnvironment rho) :
    ∀ (start : Nat) (monomial : List Nat),
      Q'.abs (evalMonoFrom rho start monomial) ≤ (1 : Q')
  | _, [] => by
      change Q'.abs (1 : Q') ≤ (1 : Q')
      decide
  | start, exponent :: rest => by
      unfold evalMonoFrom
      exact Q'.le_trans' _ _ _
        (ExpNeg.abs_mul_le
          (qpow (rho start) exponent)
          (evalMonoFrom rho (start + 1) rest))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg
            (qpow_abs_le_one (hrho start) exponent)
            (evalMonoFrom_abs_le_one rho hrho (start + 1) rest)
            Q'.zero_le_one (Q'.abs_nonneg _))
          (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

/-- Every monomial is bounded by one on the compact coordinate cube. -/
theorem evalMono_abs_le_one
    (rho : Nat → Q') (hrho : CompactCubeEnvironment rho)
    (monomial : List Nat) :
    Q'.abs (evalMono rho monomial) ≤ (1 : Q') :=
  evalMonoFrom_abs_le_one rho hrho 0 monomial

/-- The value of a finite rational polynomial on the compact cube is bounded
by the syntactic sum of the absolute values of its coefficients. -/
theorem evalRatPoly_abs_le_coefficientL1
    (rho : Nat → Q') (hrho : CompactCubeEnvironment rho) :
    ∀ polynomial : RatPoly,
      Q'.abs (evalRatPoly rho polynomial) ≤
        polynomialCoefficientL1 polynomial
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | term :: rest => by
      change
        Q'.abs
            (term.2 * evalMono rho term.1 +
              evalRatPoly rho rest) ≤
          Q'.abs term.2 + polynomialCoefficientL1 rest
      exact Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (term.2 * evalMono rho term.1)
          (evalRatPoly rho rest))
        (Q'.le_trans' _ _ _
          (ExpNeg.add_le_add2
            (ExpNeg.abs_mul_le term.2 (evalMono rho term.1))
            (evalRatPoly_abs_le_coefficientL1 rho hrho rest))
          (ExpNeg.add_le_add2
            (Q'.le_trans' _ _ _
              (Q'.mul_le_mul_of_nonneg_left
                (Q'.abs (evalMono rho term.1)) 1
                (Q'.abs term.2)
                (evalMono_abs_le_one rho hrho term.1)
                (Q'.abs_nonneg term.2))
              (Q'.le_of_eqv
                (Q'.mul_one_eqv (Q'.abs term.2))))
            (Q'.le_refl' _)))

/-- Exact rational compact-cube ceiling for the three-colour action. -/
def compactCoupledBF4ActionCeiling : Q' :=
  Q'.mkPos 133 4 (by decide)

/-- The coefficient norm computed from the literal coupled `(K,S)`
polynomial is exactly `133/4`. -/
theorem compactCoupledBF4ActionL1_exact :
    compactCoupledBF4ActionL1 ≈
      compactCoupledBF4ActionCeiling := by
  decide

/-- The genuine compact BF4 action is nonnegative at every rational
environment, by its exact LDL certificates. -/
theorem compactCoupledBF4Action_nonnegative
    (rho : Nat → Q') :
    (0 : Q') ≤
      evalRatPoly rho compactCoupledBF4ActionPolynomial := by
  have hphysical :
      (0 : Q') ≤
        coupledBF4LieAction
          (sourceLieEnvironment rho)
          (targetLieEnvironment rho) :=
    coupledBF4LieAction_nonnegative _ _
  exact Q'.le_trans' _ _ _ hphysical
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (eval_compactCoupledBF4ActionPolynomial rho)))

/-- Exact compact-domain upper bound `A ≤ 133/4`. -/
theorem compactCoupledBF4Action_le_ceiling
    (rho : Nat → Q') (hrho : CompactCubeEnvironment rho) :
    evalRatPoly rho compactCoupledBF4ActionPolynomial ≤
      compactCoupledBF4ActionCeiling := by
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_abs_self
        (evalRatPoly rho compactCoupledBF4ActionPolynomial))
      (evalRatPoly_abs_le_coefficientL1
        rho hrho compactCoupledBF4ActionPolynomial))
    (Q'.le_of_eqv compactCoupledBF4ActionL1_exact)

/-- The complete spacing-independent compact action window. -/
theorem compactCoupledBF4Action_window
    (rho : Nat → Q') (hrho : CompactCubeEnvironment rho) :
    (0 : Q') ≤
        evalRatPoly rho compactCoupledBF4ActionPolynomial ∧
      evalRatPoly rho compactCoupledBF4ActionPolynomial ≤
        compactCoupledBF4ActionCeiling :=
  ⟨compactCoupledBF4Action_nonnegative rho,
   compactCoupledBF4Action_le_ceiling rho hrho⟩

end YMGap.Continuum.BF4CompactCoupledActionBounds

#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.evalMono_abs_le_one
#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.evalRatPoly_abs_le_coefficientL1
#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.compactCoupledBF4ActionL1_exact
#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.compactCoupledBF4Action_nonnegative
#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.compactCoupledBF4Action_le_ceiling
#print axioms YMGap.Continuum.BF4CompactCoupledActionBounds.compactCoupledBF4Action_window
