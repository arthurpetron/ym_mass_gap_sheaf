/-
# Relative polynomial operator bounds on ORIGINAL represented cyclic limits

Two-sided original pairing convergence passes a relative row norm bound
to the SAME row limits. The explicit error budget is epsilon/(C+1).
The mapped-limit pin identifies the resulting bound with the actual
polynomial operator, without retaining its coarse coefficient factor.

In particular every constructed Bernstein symbol vector satisfies
||p(T2)F(T2)v||^2<=M^2||F(T2)v||^2 when |p|<=M on [0,1]. The image
representative and rate are returned. This is polynomial action on
continuous symbol vectors, not full continuous-symbol operator calculus
or physical-scale/continuum control. SU(2) nome and spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
import YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound
import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound

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
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicOperatorBound
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinRow_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (nested_error)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem comparison_error_budget (C : Q') (hC : (0 : Q')≤C) (epsilon : Q') :
    Q'.eqv (C*linearTolerance C hC epsilon+linearTolerance C hC epsilon) epsilon :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)))
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _))) (linearTolerance_total C hC epsilon)

/-- The relative bound passes to actual original limits, not a replacement norm. -/
theorem rowLimit_norm_comparison (R S : CauchyRows) (C : Q') (hC : (0 : Q')≤C)
    (h : ∀ n,RCle (completedInner (rowPoint R n) (rowPoint R n))
      (RCscale C (completedInner (rowPoint S n) (rowPoint S n)))) :
    RCle (completedInner (rowLimit R) (rowLimit R))
      (RCscale C (completedInner (rowLimit S) (rowLimit S))) := by
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let d := linearTolerance C hC epsilon
  have hd : (0 : Q')<d := linearTolerance_pos C hC he
  let n := max (pairingModulus R R d) (pairingModulus S S d)
  have hR := (row_pairing_bound R R d hd n (Nat.le_max_left _ _)).2
  have hS := (row_pairing_bound S S d hd n (Nat.le_max_right _ _)).1
  have hb := RCle_trans hR (RCadd_le_add (RCle_trans (h n) (RCscale_mono hC hS)) (RCle_refl _))
  rw [RCscale_RCadd] at hb
  change RCle (completedInner (rowLimit R) (rowLimit R))
    (RCadd (RCadd (RCscale C (completedInner (rowLimit S) (rowLimit S))) (rat (C*d))) (rat d)) at hb
  rw [nested_error] at hb
  exact RCle_trans hb (RCadd_le_add (RCle_refl _)
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv (comparison_error_budget C hC epsilon))))

/-- Any represented family of cyclic polynomial vectors; no global quotient completeness. -/
theorem cyclicLimit_norm_bound (p : QPoly.Poly) (R : CauchyRows) (q : Nat → QPoly.Poly)
    (hpin : ∀ n,rowPoint R n=polynomialOperator (q n) unitProbe.val)
    (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M) :
    RCle (completedInner (polynomialOperator p (rowLimit R)) (polynomialOperator p (rowLimit R)))
      (RCscale (M*M) (completedInner (rowLimit R) (rowLimit R))) := by
  have hrow : ∀ n,RCle (completedInner (rowPoint (operatorRows p R) n) (rowPoint (operatorRows p R) n))
      (RCscale (M*M) (completedInner (rowPoint R n) (rowPoint R n))) := by
    intro n
    rw [operatorRows_pin,hpin]
    exact cyclic_norm_bound p (q n) M hM hp
  have h := rowLimit_norm_comparison (operatorRows p R) R (M*M) (SumOfSquares.q_mul_self_nonneg M) hrow
  rw [operator_rowLimit] at h
  exact h

/-- The sharp relative bound now holds on each constructed ORIGINAL continuous symbol vector. -/
theorem continuousProbe_operator_norm_bound (p : QPoly.Poly) (M : Q') (hM : (0 : Q')≤M)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (QPoly.eval p t)≤M)
    (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    RCle (completedInner (polynomialOperator p (continuousProbe F V)) (polynomialOperator p (continuousProbe F V)))
      (RCscale (M*M) (completedInner (continuousProbe F V) (continuousProbe F V))) :=
  cyclicLimit_norm_bound p (bernsteinRows F V) (bernsteinPoly F) (bernsteinRow_pin F V) M hM hp

def continuousActionRepresentative (p : QPoly.Poly) (F : CtsMod) (V : MonotoneOmegaVanishing F) : seminorm.Cauchy :=
  actionRepresentative p (bernsteinRows F V)

def continuousActionModulus (p : QPoly.Poly) (F : CtsMod) (V : MonotoneOmegaVanishing F) : Q' → Nat :=
  actionModulus p (bernsteinRows F V)

theorem continuousAction_pin (p : QPoly.Poly) (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    Quotient.mk seminorm.completionSetoid (continuousActionRepresentative p F V)=
      polynomialOperator p (continuousProbe F V) := actionRepresentative_pin p (bernsteinRows F V)

theorem continuousAction_bound (p : QPoly.Poly) (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : continuousActionModulus p F V epsilon≤n) :
    RCle (completedDist (polynomialOperator (QPoly.pmul p (bernsteinPoly F n)) unitProbe.val)
      (polynomialOperator p (continuousProbe F V))) (rat epsilon) := by
  have h := action_bound p (bernsteinRows F V) epsilon he n hn
  rw [bernsteinRow_pin] at h
  rw [operator_mul]
  exact h

def continuousActionCertificate (p : QPoly.Poly) (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    Σ' X : seminorm.Cauchy,
      {rate : Q' → Nat // Quotient.mk seminorm.completionSetoid X=polynomialOperator p (continuousProbe F V) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (QPoly.pmul p (bernsteinPoly F n)) unitProbe.val)
            (Quotient.mk seminorm.completionSetoid X)) (rat epsilon)} := by
  refine ⟨continuousActionRepresentative p F V,⟨continuousActionModulus p F V,⟨continuousAction_pin p F V,?_⟩⟩⟩
  intro epsilon he n hn
  rw [continuousAction_pin]
  exact continuousAction_bound p F V epsilon he n hn

end YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.comparison_error_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.rowLimit_norm_comparison
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.cyclicLimit_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousProbe_operator_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousActionRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousActionModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousAction_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousAction_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLimitBound.continuousActionCertificate
