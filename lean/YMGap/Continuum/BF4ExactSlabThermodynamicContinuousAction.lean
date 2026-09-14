/-
# Constructed continuous-symbol action on represented ORIGINAL cyclic vectors

For each bounded symbol with its existing constructive continuity data,
Bernstein polynomials act by the actual original T2. The proved relative
cyclic polynomial bound constructs their Cauchy modulus on the represented
input. The original completion then supplies the action value, its Cauchy
representative and an explicit convergence rate. The sharp symbol norm
bound survives. No image-Cauchy premise or diagonal resolution is supplied.

This acts on represented cyclic inputs. Closure of its output in that
represented sector and the full continuous operator algebra are subsequent
obligations, as are physical-scale and continuum control.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (actionRepresentative actionRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinPoly_abs_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (row_pairing_bound pairingModulus)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def symbolRows (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : CauchyRows where
  row := fun n => actionRepresentative (bernsteinPoly F n) X.rows
  modulus := fun epsilon => bernsteinModulus F V (approximationTolerance X epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    simp only [actionRepresentative_pin]
    exact polynomial_close X _ _ epsilon he
      (bernstein_uniformCauchy F V _ (approximationTolerance_pos X he) m n hm hn)

theorem symbolRows_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) (n : Nat) :
    rowPoint (symbolRows F V X) n=polynomialOperator (bernsteinPoly F n) (state X) := actionRepresentative_pin _ _

def symbolAction (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : Completion :=
  rowLimit (symbolRows F V X)

def symbolRepresentative (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : seminorm.Cauchy :=
  diagonalCauchy (symbolRows F V X)

def symbolModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) : Q' → Nat :=
  rowLimitRate (symbolRows F V X)

theorem symbolRepresentative_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) :
    Quotient.mk seminorm.completionSetoid (symbolRepresentative F V X)=symbolAction F V X := rfl

theorem symbolAction_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : symbolModulus F V X epsilon≤n) :
    RCle (completedDist (polynomialOperator (bernsteinPoly F n) (state X)) (symbolAction F V X)) (rat epsilon) := by
  have h := rowLimit_bound (symbolRows F V X) epsilon he n hn
  rw [symbolRows_pin] at h
  exact h

/-- A constant RC upper bound, with no selected representative or rational-value premise. -/
theorem rowLimit_norm_upper (R : CauchyRows) (b : RC)
    (h : ∀ n,RCle (completedInner (rowPoint R n) (rowPoint R n)) b) :
    RCle (completedInner (rowLimit R) (rowLimit R)) b := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus R R epsilon
  exact RCle_trans (row_pairing_bound R R epsilon he n (Nat.le_refl n)).2
    (RCadd_le_add (h n) (RCle_refl _))

/-- The symbol sup bound controls the SAME original input norm, without a coefficient loss. -/
theorem symbolAction_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) :
    RCle (completedInner (symbolAction F V X) (symbolAction F V X))
      (RCscale (F.bound*F.bound) (completedInner (state X) (state X))) := by
  apply rowLimit_norm_upper (symbolRows F V X)
  intro n
  rw [symbolRows_pin]
  exact polynomial_norm_bound X _ F.bound (bound_nonneg F) (bernsteinPoly_abs_bound F n)

def symbolActionCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F) (X : CyclicPresentation) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // Quotient.mk seminorm.completionSetoid Y=symbolAction F V X ∧
        (∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (bernsteinPoly F n) (state X))
            (Quotient.mk seminorm.completionSetoid Y)) (rat epsilon)) ∧
        RCle (completedInner (Quotient.mk seminorm.completionSetoid Y) (Quotient.mk seminorm.completionSetoid Y))
          (RCscale (F.bound*F.bound) (completedInner (state X) (state X)))} :=
  ⟨symbolRepresentative F V X,⟨symbolModulus F V X,⟨rfl,symbolAction_bound F V X,symbolAction_norm_bound F V X⟩⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolAction_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.rowLimit_norm_upper
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolAction_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction.symbolActionCertificate
