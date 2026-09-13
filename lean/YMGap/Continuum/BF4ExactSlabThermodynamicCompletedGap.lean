/-
# Strict form gap on the SAME original completed unit complement

The centered pairings of supplied original Cauchy presentations converge
to the centered completed pairing. This is proved from the existing three
pairing limits and the exact rank-one centering formula, with their original
moduli retained. The dense two-step bound passes through those SAME limits.
Quotient elimination then gives, for every completed unit-orthogonal vector,

  0 <= <v,T_2 v> <= (1/2)<v,v>.

The operator is the original geometric two-step OS time translation, not
link-variable heat-bath dynamics. Nome 1/1024 and lattice spacing are fixed.
No nonzero excitation, full required observable-algebra completeness,
continuous-time generator or continuum/Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection (unitCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeStates (timeState_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicDenseGap
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

local notation "D" => seminorm
local notation "B" => completedInner

def centeredSequence (X Y : (D).Cauchy) (n : Nat) : CReal :=
  CReal.sub (pairSequence X Y n) (CReal.mul (pairSequence X unitCauchy n) (pairSequence unitCauchy Y n))

def centeredLimit (X Y : (D).Cauchy) : CReal :=
  CReal.sub (representativeInner X Y)
    (CReal.mul (representativeInner X unitCauchy) (representativeInner unitCauchy Y))

def centeredLimitCauchy (X Y : (D).Cauchy) : QCauchy (centeredLimit X Y).approx :=
  scalarAddCauchy _ _ (representativeInnerCauchy X Y)
    (scalarNegCauchy _ (scalarMulCauchy _ _ (representativeInnerCauchy X unitCauchy) (representativeInnerCauchy unitCauchy Y)))

theorem centeredSequence_pin (X Y : (D).Cauchy) (n : Nat) :
    B (center (embedPresentation (X.seq n))) (center (embedPresentation (Y.seq n))) =
      Quotient.mk crealSetoid (centeredSequence X Y n) := by
  rw [centered_inner]
  change RCsub (B (embedPresentation (X.seq n)) (embedPresentation (Y.seq n)))
    (RCmul (B (embedPresentation (X.seq n)) (embedPresentation one))
      (B (embedPresentation one) (embedPresentation (Y.seq n)))) = _
  rw [completedInner_embedPresentation, completedInner_embedPresentation, completedInner_embedPresentation]
  rfl

theorem centeredLimit_pin (X Y : (D).Cauchy) :
    B (center (Quotient.mk (D).completionSetoid X)) (center (Quotient.mk (D).completionSetoid Y)) =
      Quotient.mk crealSetoid (centeredLimit X Y) := by
  rw [centered_inner]
  rfl

theorem centeredSequence_converges (X Y : (D).Cauchy) : ConvergesTo (centeredSequence X Y) (centeredLimit X Y) :=
  convergesTo_add (pairSequence_converges X Y)
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (pairSequence_converges X unitCauchy) (pairSequence_converges unitCauchy Y)))

theorem centeredSequence_gap (X : (D).Cauchy) (n : Nat) :
    leEv (centeredSequence X (timeCauchy 2 X) n) (CReal.mul (ofQ' HalfPow.half) (centeredSequence X X n)) := by
  have h := dense_twoStep_form_gap (X.seq n)
  unfold twoStepTransfer at h
  rw [completedTime_center, completedTime_embedPresentation, timeState_pin] at h
  change RCle (B (center (embedPresentation (X.seq n))) (center (embedPresentation ((timeCauchy 2 X).seq n))))
    (RCscale HalfPow.half (B (center (embedPresentation (X.seq n))) (center (embedPresentation (X.seq n))))) at h
  rw [centeredSequence_pin, centeredSequence_pin] at h
  exact h

theorem centeredLimit_gap (X : (D).Cauchy) :
    leEv (centeredLimit X (timeCauchy 2 X)) (CReal.mul (ofQ' HalfPow.half) (centeredLimit X X)) :=
  leEv_of_convergesTo_le (centeredSequence_converges X (timeCauchy 2 X))
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (convergesTo_const _) (centeredSequence_converges X X)) (centeredSequence_gap X)

/-- No representative is chosen; the gap is proved for every quotient class. -/
theorem centered_twoStep_form_gap (x : Completion) :
    RCle (B (center x) (twoStepTransfer (center x))) (RCscale HalfPow.half (B (center x) (center x))) := by
  refine Quotient.inductionOn x ?_
  intro X
  unfold twoStepTransfer
  rw [completedTime_center, completedTime_mk, centeredLimit_pin, centeredLimit_pin]
  exact centeredLimit_gap X

/-- The actual completed unit complement, with a common strict constant. -/
theorem complement_twoStep_form_gap (v : UnitComplement) :
    RCnonneg (B v.val (twoStepTransfer v.val)) ∧
      RCle (B v.val (twoStepTransfer v.val)) (RCscale HalfPow.half (B v.val v.val)) := by
  have h := centered_twoStep_form_gap v.val
  rw [(center_fixed_iff v.val).mpr v.property] at h
  exact ⟨twoStepTransfer_positive v.val, h⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredSequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredSequence_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredSequence_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centeredLimit_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.centered_twoStep_form_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap.complement_twoStep_form_gap
