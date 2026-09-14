/-
# Polynomial action commutes with represented ORIGINAL carrier limits

Actual original Cauchy rows are mapped by the already-constructed finite
time/scalar/addition representative. The explicit coefficient continuity
tolerance supplies their outer modulus. The constructed image limit is
proved equal to the existing polynomial operator on the original limit.
The image representative and convergence rate are retained as data.
No quotient representative is selected or operator action postulated.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (vectorRepresentative vectorRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def operatorRows (p : QPoly.Poly) (R : CauchyRows) : CauchyRows where
  row := fun n => vectorRepresentative (R.row n) p 0
  modulus := fun epsilon => R.modulus (operatorTolerance p epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    simp only [vectorRepresentative_pin]
    exact operator_close p _ _ epsilon he
      (R.isCauchy _ (operatorTolerance_pos p he) m n hm hn)

theorem operatorRows_pin (p : QPoly.Poly) (R : CauchyRows) (n : Nat) :
    rowPoint (operatorRows p R) n=polynomialOperator p (rowPoint R n) := vectorRepresentative_pin _ _ _

def actionModulus (p : QPoly.Poly) (R : CauchyRows) (epsilon : Q') : Nat :=
  rowLimitRate R (operatorTolerance p epsilon)

theorem action_bound (p : QPoly.Poly) (R : CauchyRows) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : actionModulus p R epsilon≤n) :
    RCle (completedDist (polynomialOperator p (rowPoint R n)) (polynomialOperator p (rowLimit R))) (rat epsilon) :=
  operator_close p _ _ epsilon he (rowLimit_bound R _ (operatorTolerance_pos p he) n hn)

/-- The constructed image limit is the SAME pre-existing polynomial operator value. -/
theorem operator_rowLimit (p : QPoly.Poly) (R : CauchyRows) :
    rowLimit (operatorRows p R)=polynomialOperator p (rowLimit R) := by
  apply rowLimit_eq_of_bound _ _ (actionModulus p R)
  intro epsilon he n hn
  rw [operatorRows_pin]
  exact action_bound p R epsilon he n hn

def actionRepresentative (p : QPoly.Poly) (R : CauchyRows) : seminorm.Cauchy :=
  diagonalCauchy (operatorRows p R)

theorem actionRepresentative_pin (p : QPoly.Poly) (R : CauchyRows) :
    Quotient.mk seminorm.completionSetoid (actionRepresentative p R)=polynomialOperator p (rowLimit R) :=
  operator_rowLimit p R

def actionCertificate (p : QPoly.Poly) (R : CauchyRows) :
    Σ' X : seminorm.Cauchy,
      {rate : Q' → Nat // Quotient.mk seminorm.completionSetoid X=polynomialOperator p (rowLimit R) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator p (rowPoint R n))
            (Quotient.mk seminorm.completionSetoid X)) (rat epsilon)} := by
  refine ⟨actionRepresentative p R,⟨actionModulus p R,⟨actionRepresentative_pin p R,?_⟩⟩⟩
  intro epsilon he n hn
  rw [actionRepresentative_pin]
  exact action_bound p R epsilon he n hn

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.operatorRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.operatorRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.actionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.action_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.operator_rowLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.actionRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.actionRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction.actionCertificate
