/-
# Algebraic operations on the completed physical BF4 cutoff carrier

`BF4PhysicalCutoffLinearCompletion` constructs the radical quotient and
explicit-modulus Cauchy completion of the cutoff-removed physical form.  This
module descends the operations needed for a physical linear state carrier.

Addition satisfies the generic sqrt-free binary quadratic-Lipschitz estimate.
Rational scaling multiplies squared distance by `s^2`, so the explicit
`scaleTolerance` modulus makes every scalar action uniformly continuous.
Zero is the embedded zero presentation and negation is scaling by `-1`.

The declarations here construct the operations.  Their completed module laws
are a separate quotient-level frontier.  No cutoff-independent transfer,
strict gap, thermodynamic limit, or continuum theory is asserted.

## Axiom gate

Only the proved finite physical GNS laws, constructive-real continuity
moduli, and quotient descent are used.  There is no classical choice,
noncomputable declaration, custom axiom, or unproved placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar

local infix:50 " ≈ " => Q'.eqv

private theorem leEv_of_approx_le {left right : CReal}
    (h : forall cutoff, left.approx cutoff <= right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨0, fun cutoff _ =>
    Q'.le_trans' _ _ _ (h cutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

/-! ## 1. Addition is binary quadratic-Lipschitz -/

theorem physicalLinearDistSq_add_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left left' right right' : CentralPhysicalLinearObservable) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (add left right) (add left' right'))
      (CReal.add
        (CReal.add
          (physicalLinearDistSq hw0 hw1 half left left')
          (physicalLinearDistSq hw0 hw1 half left left'))
        (CReal.add
          (physicalLinearDistSq hw0 hw1 half right right')
          (physicalLinearDistSq hw0 hw1 half right right'))) :=
  leEv_of_approx_le (fun cutoff => by
    let D := (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
    have hsum := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff (add left right) (add left' right')
    have hleft := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff left left'
    have hright := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff right right'
    have hbound := D.distSqQ_add_le
      left.value right.value left'.value right'.value
    have htarget :
        ((D.distSqQ left.value left'.value +
            D.distSqQ left.value left'.value) +
          (D.distSqQ right.value right'.value +
            D.distSqQ right.value right'.value)) ≈
        (((physicalLinearDistSq hw0 hw1 half left left').approx cutoff +
            (physicalLinearDistSq hw0 hw1 half left left').approx cutoff) +
          ((physicalLinearDistSq hw0 hw1 half right right').approx cutoff +
            (physicalLinearDistSq hw0 hw1 half right right').approx cutoff)) :=
      Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_symm hleft) (Q'.eqv_symm hleft))
        (Q'.add_eqv_congr' (Q'.eqv_symm hright) (Q'.eqv_symm hright))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv htarget)))

def physicalLinearAddQuadraticLipschitz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).BinaryQuadraticLipschitz where
  toFun := add
  contraction := physicalLinearDistSq_add_le hw0 hw1 half

/-- Addition on the completed cutoff-removed physical carrier. -/
def completedPhysicalLinearAdd
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
        CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  (physicalLinearAddQuadraticLipschitz hw0 hw1 half).completionMap

/-! ## 2. Rational scaling has an explicit continuity modulus -/

private theorem creal_mul_congr_right
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

theorem physicalLinearDistSq_smul_equiv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (left right : CentralPhysicalLinearObservable) :
    CReal.Equiv
      (physicalLinearDistSq hw0 hw1 half
        (smul scalar left) (smul scalar right))
      (CReal.mul (CReal.ofQ' (scalar * scalar))
        (physicalLinearDistSq hw0 hw1 half left right)) :=
  Equiv_of_approx_eqv (fun cutoff => by
    let S := centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half
    have hscaled := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff (smul scalar left) (smul scalar right)
    have horiginal := physicalLinearDistSq_approx_eqv_stage
      hw0 hw1 half cutoff left right
    exact Q'.eqv_trans _ _ _ hscaled
      (Q'.eqv_trans _ _ _
        (S.distSqQ_smul scalar left.value right.value)
        (Q'.mul_eqv_congr_left (scalar * scalar) _ _
          (Q'.eqv_symm horiginal))))

def physicalLinearSmulContinuous
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q') :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).ModulusContinuous where
  toFun := smul scalar
  tolerance := CReal.InnerRegularity.scaleTolerance (scalar * scalar)
  tolerance_pos := fun epsilon hepsilon =>
    CReal.InnerRegularity.scaleTolerance_pos
      (scalar * scalar) epsilon hepsilon
  contraction := by
    intro epsilon hepsilon left right hdist
    have hsq : (0 : Q') <= scalar * scalar :=
      SumOfSquares.q_mul_self_nonneg scalar
    have hscaled := CReal.leEv_smul_nonneg hsq hdist
    have hconstant : CReal.leEv
        (CReal.mul (CReal.ofQ' (scalar * scalar))
          (CReal.ofQ'
            (CReal.InnerRegularity.scaleTolerance
              (scalar * scalar) epsilon)))
        (CReal.ofQ' epsilon) := by
      have hproduct := CReal.InnerRegularity.mul_scaleTolerance_le
        (scalar * scalar) epsilon hsq hepsilon
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          (CReal.Equiv.symm (CRealAlg.ofQ'_mul (scalar * scalar)
            (CReal.InnerRegularity.scaleTolerance
              (scalar * scalar) epsilon))))
        (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hproduct))
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (physicalLinearDistSq_smul_equiv
          hw0 hw1 half scalar left right))
      (CReal.leEv_trans hscaled hconstant)

/-- Rational scaling on the completed cutoff-removed physical carrier. -/
def completedPhysicalLinearSmul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q') :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  (physicalLinearSmulContinuous hw0 hw1 half scalar).completionMap

/-! ## 3. Completed zero and negation -/

/-- Zero in the completed cutoff-removed physical carrier. -/
def completedPhysicalLinearZero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  embedCentralPhysicalLinearObservable hw0 hw1 half zero

/-- Negation on the completed carrier, constructed as scaling by `-1`. -/
def completedPhysicalLinearNeg
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  completedPhysicalLinearSmul hw0 hw1 half (-1)

/-! ## Axiom audit -/

#print axioms physicalLinearDistSq_add_le
#print axioms physicalLinearAddQuadraticLipschitz
#print axioms completedPhysicalLinearAdd
#print axioms physicalLinearDistSq_smul_equiv
#print axioms physicalLinearSmulContinuous
#print axioms completedPhysicalLinearSmul
#print axioms completedPhysicalLinearZero
#print axioms completedPhysicalLinearNeg

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
