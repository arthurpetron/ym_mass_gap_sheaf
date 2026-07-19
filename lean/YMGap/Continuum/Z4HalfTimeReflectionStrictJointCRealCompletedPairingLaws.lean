/-
# Dense compatibility and shift-one self-adjointness after completion

This leaf transfers the algebraic laws of the strict reflection pairing to the
actual staged-seminorm completion.  Its reusable engine applies constructive
uniqueness of limits to pointwise-equivalent raw pairing sequences.  It then
proves constant/dense compatibility, symmetry, one-sided shift-one covariance,
and shift-one self-adjointness.

The arbitrary completed-vector laws are obtained by quotient induction on
explicit Cauchy representatives.  Dense compatibility is proved separately as
a validation theorem; no surjectivity or unformalized density-continuity
principle is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingDescent
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitCompletionBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepDirectLimitSelfAdjointness

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCanonicalPairingCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingRawOuterRate
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitCompletionBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepDirectLimitSelfAdjointness
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

variable {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
  (hle : coupling <= anchorCoupling)

private abbrev StageSeminorm : SquaredSeminorm :=
  strictJointCylinderStageSquaredSeminorm hcoupling hle

private abbrev StageTimeOne :
    (StageSeminorm hcoupling hle).Nonexpansive :=
  strictJointCylinderStageTimeTranslateNonexpansive hcoupling hle 1

/-! ## 1. A reusable limit-transfer engine -/

/-- Pointwise equivalence of the raw polarized pairing sequences transfers to
equivalence of their canonically completed representative limits. -/
theorem strictJointCylinderRepresentativePairingLimit_equiv_of_raw_sequence
    (X Y X' Y' : (StageSeminorm hcoupling hle).Cauchy)
    (hraw : forall n : Nat, CReal.Equiv
      (strictJointCylinderPairingSequence hcoupling hle X Y n)
      (strictJointCylinderPairingSequence hcoupling hle X' Y' n)) :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit hcoupling hle X Y)
      (strictJointCylinderRepresentativePairingLimit hcoupling hle X' Y') := by
  exact CReal.Equiv_of_limit_of_equal
    (fun n => CReal.Equiv.trans
      (strictJointCylinderCanonicalPairingSequence_equiv_raw
        hcoupling hle X Y n)
      (CReal.Equiv.trans (hraw n)
        (CReal.Equiv.symm
          (strictJointCylinderCanonicalPairingSequence_equiv_raw
            hcoupling hle X' Y' n))))
    (strictJointCylinderRepresentativePairingLimit_converges
      hcoupling hle X Y)
    (strictJointCylinderRepresentativePairingLimit_converges
      hcoupling hle X' Y')

/-! ## 2. Dense compatibility -/

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ : Nat => value) value := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ⟨0, fun n _ => ?_⟩⟩
  exact
    ⟨Q'.add_le_self_of_nonneg (value.approx n) epsilon
        (Q'.le_of_lt hepsilon),
      Q'.add_le_self_of_nonneg (value.approx n) epsilon
        (Q'.le_of_lt hepsilon)⟩

/-- The representative pairing of two constant Cauchy sequences recovers the
original staged pairing. -/
theorem strictJointCylinderRepresentativePairingLimit_constant_equiv_stage
    (left right :
      (StageSeminorm hcoupling hle).Carrier) :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit hcoupling hle
        ((StageSeminorm hcoupling hle).constant left)
        ((StageSeminorm hcoupling hle).constant right))
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := strictJointCylinderCanonicalPairingSequence hcoupling hle
      ((StageSeminorm hcoupling hle).constant left)
      ((StageSeminorm hcoupling hle).constant right))
    (bSeq := fun _ => strictJointCylinderStageReflectionBilinear
      hcoupling hle left right)
  · intro n
    simpa only [strictJointCylinderPairingSequence,
      SquaredSeminorm.constant] using
      (strictJointCylinderCanonicalPairingSequence_equiv_raw
        hcoupling hle
        ((StageSeminorm hcoupling hle).constant left)
        ((StageSeminorm hcoupling hle).constant right) n)
  · exact strictJointCylinderRepresentativePairingLimit_converges
      hcoupling hle
      ((StageSeminorm hcoupling hle).constant left)
      ((StageSeminorm hcoupling hle).constant right)
  · exact convergesTo_const
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right)

/-- On the dense constant embedding, the completed pairing is the original
staged reflection form. -/
@[simp] theorem strictJointCylinderCompletedPairing_embedRep
    (left right : (StageSeminorm hcoupling hle).Carrier) :
    strictJointCylinderCompletedPairing hcoupling hle
        ((StageSeminorm hcoupling hle).embedRep left)
        ((StageSeminorm hcoupling hle).embedRep right) =
      Quotient.mk CReal.crealSetoid
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right) := by
  exact Quotient.sound
    (strictJointCylinderRepresentativePairingLimit_constant_equiv_stage
      hcoupling hle left right)

/-- The completed pairing extends the algebraic direct-limit pairing along
the canonical map into the OS completion. -/
theorem StrictJointCylinderDirectLimit.toOSCompletion_pairing
    (left right : StrictJointCylinderDirectLimit) :
    strictJointCylinderCompletedPairing hcoupling hle
        (StrictJointCylinderDirectLimit.toOSCompletion hcoupling hle left)
        (StrictJointCylinderDirectLimit.toOSCompletion hcoupling hle right) =
      StrictJointCylinderDirectLimit.reflectionBilinear
        hcoupling hle left right := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftStage rightStage
  exact strictJointCylinderCompletedPairing_embedRep
    hcoupling hle leftStage rightStage

/-! ## 3. Symmetry on representatives and the completed carrier -/

theorem strictJointCylinderRepresentativePairingLimit_symm
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit hcoupling hle X Y)
      (strictJointCylinderRepresentativePairingLimit hcoupling hle Y X) := by
  apply strictJointCylinderRepresentativePairingLimit_equiv_of_raw_sequence
    hcoupling hle X Y Y X
  intro n
  simpa only [strictJointCylinderPairingSequence] using
    (strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle (X.seq n) (Y.seq n))

/-- Symmetry of the completed strict reflection pairing. -/
theorem strictJointCylinderCompletedPairing_symm
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedPairing hcoupling hle left right =
      strictJointCylinderCompletedPairing hcoupling hle right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (strictJointCylinderRepresentativePairingLimit_symm
      hcoupling hle X Y)

/-! ## 4. Shift-one covariance and self-adjointness -/

theorem strictJointCylinderRepresentativePairingLimit_oneSidedTimeCovariance_one
    (X Y : (StageSeminorm hcoupling hle).Cauchy) :
    CReal.Equiv
      (strictJointCylinderRepresentativePairingLimit hcoupling hle
        X ((StageTimeOne hcoupling hle).mapCauchy Y))
      (strictJointCylinderRepresentativePairingLimit hcoupling hle
        Y ((StageTimeOne hcoupling hle).mapCauchy X)) := by
  apply strictJointCylinderRepresentativePairingLimit_equiv_of_raw_sequence
    hcoupling hle
      X ((StageTimeOne hcoupling hle).mapCauchy Y)
      Y ((StageTimeOne hcoupling hle).mapCauchy X)
  intro n
  change CReal.Equiv
    (strictJointCylinderStageReflectionBilinear hcoupling hle
      (X.seq n) ((Y.seq n).timeTranslate 1))
    (strictJointCylinderStageReflectionBilinear hcoupling hle
      (Y.seq n) ((X.seq n).timeTranslate 1))
  exact strictJointCylinderStage_oneSidedTimeCovariance_one_derived
    hcoupling hle (X.seq n) (Y.seq n)

/-- One-sided shift-one covariance on arbitrary completed vectors. -/
theorem strictJointCylinderCompletedPairing_oneSidedTimeCovariance_one
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedPairing hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right) =
      strictJointCylinderCompletedPairing hcoupling hle right
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left) := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (strictJointCylinderRepresentativePairingLimit_oneSidedTimeCovariance_one
      hcoupling hle X Y)

/-- The completed shift-one time action is self-adjoint for the completed
strict reflection pairing. -/
theorem strictJointCylinderCompletedTimeTranslate_one_selfAdjoint
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedPairing hcoupling hle
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left) right =
      strictJointCylinderCompletedPairing hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right) := by
  calc
    strictJointCylinderCompletedPairing hcoupling hle
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left) right =
      strictJointCylinderCompletedPairing hcoupling hle right
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 left) :=
      strictJointCylinderCompletedPairing_symm hcoupling hle _ _
    _ = strictJointCylinderCompletedPairing hcoupling hle left
        (strictJointCylinderCompletedTimeTranslate hcoupling hle 1 right) :=
      (strictJointCylinderCompletedPairing_oneSidedTimeCovariance_one
        hcoupling hle left right).symm

#print axioms strictJointCylinderRepresentativePairingLimit_equiv_of_raw_sequence
#print axioms strictJointCylinderRepresentativePairingLimit_constant_equiv_stage
#print axioms strictJointCylinderCompletedPairing_embedRep
#print axioms StrictJointCylinderDirectLimit.toOSCompletion_pairing
#print axioms strictJointCylinderRepresentativePairingLimit_symm
#print axioms strictJointCylinderCompletedPairing_symm
#print axioms strictJointCylinderRepresentativePairingLimit_oneSidedTimeCovariance_one
#print axioms strictJointCylinderCompletedPairing_oneSidedTimeCovariance_one
#print axioms strictJointCylinderCompletedTimeTranslate_one_selfAdjoint

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedPairingLaws
