/-
# A constructed positive square root of the ORIGINAL two-step transfer

The explicit uniformly Cauchy polynomial root sequence acts on the full
original completion. Its square sequence converges to the coordinate.
Passing exact polynomial mixed pairings through the original represented
limits proves S^2=T2, without a supplied spectral model or a general
uniform-sequence multiplication theorem. S is symmetric, nonnegative,
contractive, and preserves the existing original unit complement, where
the previously proved T2 form gap gives ||Sv||^2<=half*||v||^2.

This constructs a positive square root, NOT an identification with the
geometric T1. Its kernel is proved equal to ker(T2), not proved zero.
Time injectivity, continuous-time construction, physical-scale uniformity,
continuum reconstruction, other groups and the Clay target remain open.
The original SU(2) nome 1/1024 and spacing stay fixed.
-/

import YMGap.Continuum.UniformSquareRootPolynomial
import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus

namespace YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinSequenceWrap (eval01)
open YMGap.Continuum.UniformSquareRootIteration (residualStage)
open YMGap.Continuum.UniformSquareRootPolynomial
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (completedInner_posdef)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap (complement_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus (center_polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear

local notation "point" X => Quotient.mk seminorm.completionSetoid X

def rootAction : Completion → Completion := sequenceAction rootSequence

theorem rootAction_add (x y : Completion) :
    rootAction (completedAdd x y)=completedAdd (rootAction x) (rootAction y) := sequenceAction_add _ x y

theorem rootAction_smul (c : Q') (x : Completion) :
    rootAction (completedSmul c x)=completedSmul c (rootAction x) := sequenceAction_smul _ c x

theorem rootAction_symmetric (x y : Completion) :
    completedInner (rootAction x) y=completedInner x (rootAction y) := sequenceAction_symmetric _ x y

theorem rootAction_nonnegative (x : Completion) : RCnonneg (completedInner (rootAction x) x) :=
  sequenceAction_form_nonnegative rootSequence polynomial_nonnegative x

theorem rootAction_contraction (x : Completion) :
    RCle (completedInner (rootAction x) (rootAction x)) (completedInner x x) := by
  have h := sequenceAction_tail_norm_bound rootSequence 0 1 Q'.zero_le_one
    (fun n _ => polynomial_abs_bound n) x
  rw [scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1),RCscale_one] at h
  exact h

theorem squareSequence_action (x : Completion) : sequenceAction squareSequence x=twoStepTransfer x := by
  have h := sequenceAction_congr squareSequence (constantSequence [0,1]) residualStage (by
    intro epsilon he n hn t ht h1
    exact ⟨Q'.le_trans' _ _ _ (squarePolynomial_le_coordinate n t ht h1)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (eval01 t)) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval01 t)) (coordinate_le_squarePolynomial epsilon he n hn t ht h1)⟩) x
  exact h.trans ((constantSequence_action _ x).trans (operator_coordinate x))

/-- Exact polynomial square pairings survive on the SAME original carrier. -/
theorem rootAction_pairing (x y : Completion) :
    completedInner (rootAction x) (rootAction y)=completedInner (twoStepTransfer x) y := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (actionRows rootSequence X) (actionRows rootSequence Y)
    (actionRows squareSequence X) (constantRows Y) (by
      intro n
      rw [actionRows_pin,actionRows_pin,actionRows_pin,constantRows_pin]
      change completedInner (polynomialOperator (polynomial n) (point X))
        (polynomialOperator (polynomial n) (point Y))=
          completedInner (polynomialOperator (QPoly.pmul (polynomial n) (polynomial n)) (point X)) (point Y)
      rw [operator_mul]
      exact (operator_symmetric _ _ _).symm)
  rw [rowLimit_constant] at h
  change completedInner (rootAction (point X)) (rootAction (point Y))=
    completedInner (sequenceAction squareSequence (point X)) (point Y) at h
  rw [squareSequence_action] at h
  exact h

/-- Constructed positive square root of T2; no identification with geometric T1 is asserted. -/
theorem rootAction_square (x : Completion) : rootAction (rootAction x)=twoStepTransfer x := by
  apply completed_eq_of_pairings
  intro y
  rw [rootAction_symmetric,rootAction_pairing]

theorem rootAction_commutes_twoStep (x : Completion) :
    rootAction (twoStepTransfer x)=twoStepTransfer (rootAction x) :=
  (congrArg rootAction (rootAction_square x).symm).trans (rootAction_square (rootAction x))

theorem rootAction_center (x : Completion) : rootAction (center x)=center (rootAction x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : representedAction rootSequence (centerCauchy X)=rowLimit (centeredRows (actionRows rootSequence X)) := by
    apply rowLimit_independent
    intro n
    rw [actionRows_pin,centeredRows_rowPoint,actionRows_pin]
    exact (center_polynomialVector (point X) (polynomial n) 0).symm
  exact h.trans (rowLimit_centeredRows _)

theorem rootAction_orthogonal (x : Completion) (hx : completedInner x completedUnit=RCzero) :
    completedInner (rootAction x) completedUnit=RCzero := by
  apply (center_fixed_iff _).mp
  rw [← rootAction_center,(center_fixed_iff x).mpr hx]

def complementRoot (x : UnitComplement) : UnitComplement :=
  ⟨rootAction x.val,rootAction_orthogonal x.val x.property⟩

theorem complementRoot_pin (x : UnitComplement) : (complementRoot x).val=rootAction x.val := rfl

theorem complementRoot_square (x : UnitComplement) :
    (complementRoot (complementRoot x)).val=twoStepTransfer x.val := rootAction_square x.val

/-- This is the EXISTING fixed-spacing T2 form gap on the constructed root, not a new scale-uniform gap. -/
theorem complementRoot_norm_bound (x : UnitComplement) :
    RCle (completedInner (complementRoot x).val (complementRoot x).val)
      (RCscale HalfPow.half (completedInner x.val x.val)) := by
  rw [complementRoot_pin,rootAction_pairing,completedInner_symm]
  exact (complement_twoStep_form_gap x).2

theorem rootAction_zero : rootAction completedZero=completedZero := by
  have h := rootAction_smul 0 completedZero
  simpa only [completedSmul_zero] using h

/-- The possible zero-time-kernel obstruction is preserved, not silently removed. -/
theorem rootAction_kernel (x : Completion) : rootAction x=completedZero ↔ twoStepTransfer x=completedZero := by
  constructor
  · intro h
    rw [← rootAction_square,h,rootAction_zero]
  · intro h
    apply (completedInner_posdef _).mp
    rw [rootAction_pairing,h,completedInner_zero_left]

/-- Original output Cauchy data and the computed polynomial convergence rate. -/
def rootActionCertificate (X : seminorm.Cauchy) := sequenceActionCertificate rootSequence X

end YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.squareSequence_action
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_commutes_twoStep
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.complementRoot
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.complementRoot_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.complementRoot_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.complementRoot_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootAction_kernel
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSquareRootAction.rootActionCertificate
