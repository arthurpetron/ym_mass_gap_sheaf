/-
# Extending the dense two-step gap through the strict OS completion

The dense strict-cylinder vacuum complement carries the uniform form estimate

  <S v, v> <= (1/16) <v, v>,

for the concrete completed two-step transfer `S`.  Passing that estimate to a
general completed vector by this route requires more than density in the whole
OS space: it requires a Cauchy representative whose stages lie *exactly* in the
dense vacuum kernel.  This file records that conditional analytic limit
passage.  The downstream centered-completion argument avoids and supersedes
the global exact-kernel density requirement.

The residual hypothesis is carried in `Type`.  An approximation contains its
actual Cauchy representative, an explicit-modulus `Close` witness to the
original representative (hence an exact quotient identity), and stagewise
dense vacuum orthogonality.  No choice principle is used to select it.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
import YMGap.Continuum.ContinuousFunctionalCalculusForm

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedGapExtension

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointConnectedTwoStepMoment
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The exact dense-kernel approximation witness -/

/-- Generic exact-kernel replacement data for a constructive seminorm
completion.  Keeping this record generic prevents the strict-cylinder
seminorm's large proof fields from being unfolded by the structure command.
-/
structure ExactKernelCauchyReplacement
    (D : SquaredSeminorm) (kernel : D.Carrier -> Prop)
    (original : D.Cauchy) : Type where
  representative : D.Cauchy
  close : D.Close original representative
  stageInKernel : forall n : Nat, kernel (representative.seq n)

/-- Strict-cylinder specialization of exact-kernel replacement data. -/
abbrev ExactDenseVacuumComplementReplacement
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (original :
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) : Type :=
  ExactKernelCauchyReplacement
    (strictJointCylinderStageSquaredSeminorm hcoupling hle)
    (fun stage =>
      StrictJointVacuumOrthogonal hcoupling hle stage.vector)
    original

/-- The global exact-kernel completion statement required by this conditional
route.  This is deliberately a `Type`, not a bare existence proposition,
preserving the representative and its constructive modulus.  The centered
completion route does not require an inhabitant of this type.
-/
def ExactDenseVacuumComplementDensity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) : Type :=
  forall original :
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy,
    StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle
        (Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
          original) ->
      ExactDenseVacuumComplementReplacement hcoupling hle original

/-- A literal dense vacuum-orthogonal cylinder has the required exact
representative: the constant Cauchy sequence.  Thus the residual interface
agrees definitionally with the already-proved dense theorem.
-/
def exactDenseVacuumComplementReplacement_constant
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    ExactDenseVacuumComplementReplacement hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).constant
        (StrictJointCylinderStage.mk base vector)) where
  representative :=
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).constant
      (StrictJointCylinderStage.mk base vector)
  close :=
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).closeRefl _
  stageInKernel := fun _ => horthogonal

/-! ## 2. The constructive limit passage -/

/-- If every stage of one explicit Cauchy representative is exactly
vacuum-orthogonal, the dense `1/16` estimate passes through the pairing limits.
This is the analytic completion step; both sides use the already-constructed
choice-free pairing limits and their explicit convergence moduli.
-/
theorem cauchyPairingLimit_twoStep_form_gap
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (horthogonal : forall n : Nat,
      StrictJointVacuumOrthogonal hcoupling hle (X.seq n).vector) :
    CReal.leEv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle (1 + 1)).mapCauchy X) X)
      (CReal.mul (CReal.ofQ' anchorDecoratedDoubledTimeRate)
        (cauchyPairingLimit hcoupling hle X X)) := by
  let TX := (strictJointCylinderStageTimeTranslateNonexpansive
    hcoupling hle (1 + 1)).mapCauchy X
  have htargetConverges := cauchyPairingSeq_converges
    hcoupling hle TX X
  have hsourceConverges := CReal.convergesTo_constMul
    anchorDecoratedDoubledTimeRate
    (cauchyPairingSeq_converges hcoupling hle X X)
  apply CReal.leEv_of_convergesTo_le htargetConverges hsourceConverges
  intro n
  have hn := strictJointCylinderCompletedTwoStepTransfer_embed_form_gap
    hcoupling hle (X.seq n).vector (horthogonal n)
  rw [strictJointCylinderCompletedTwoStepTransfer,
    strictJointCylinderCompletedTimeTranslate_embedRep,
    strictJointCylinderCompletedInner_embedRep,
    strictJointCylinderCompletedInner_embedRep,
    CReal.RCscale_mk, CReal.RCle_mk] at hn
  exact hn

/-- One exact dense-kernel representative is sufficient to prove the uniform
form estimate for the completed vector it represents.
-/
theorem strictJointCylinderCompletedTwoStepTransfer_form_gap_of_approximation
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (original :
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy)
    (approximation :
      ExactDenseVacuumComplementReplacement hcoupling hle original) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle
          (Quotient.mk
            (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
            original))
        (Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
          original))
      (CReal.RCscale anchorDecoratedDoubledTimeRate
        (strictJointCylinderCompletedInner hcoupling hle
          (Quotient.mk
            (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
            original)
          (Quotient.mk
            (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
            original))) := by
  have hsame :
      Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
          original =
        Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid
          approximation.representative :=
    Quotient.sound ⟨approximation.close⟩
  rw [hsame]
  exact cauchyPairingLimit_twoStep_form_gap hcoupling hle
    approximation.representative approximation.stageInKernel

/-! ## 3. Contraction to the completed form-gap property -/

/-- Exact dense-kernel approximation contracts with the analytic limit
passage to give the requested completed vacuum-complement gap, with the same
uniform separator `1/16` as on the dense carrier.
-/
theorem anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap_of_density
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (density : ExactDenseVacuumComplementDensity hcoupling hle) :
    StrictJointCylinderCompletedTwoStepVacuumFormGap
      hcoupling hle anchorDecoratedDoubledTimeRate := by
  refine ⟨anchorDecoratedDoubledTimeRate_nonnegative,
    anchorDecoratedDoubledTimeRate_lt_one, ?_⟩
  intro vector horthogonal
  revert horthogonal
  refine Quotient.inductionOn vector ?_
  intro original horthogonal
  exact strictJointCylinderCompletedTwoStepTransfer_form_gap_of_approximation
    hcoupling hle original (density original horthogonal)

#print axioms ExactKernelCauchyReplacement
#print axioms ExactDenseVacuumComplementReplacement
#print axioms ExactDenseVacuumComplementDensity
#print axioms exactDenseVacuumComplementReplacement_constant
#print axioms cauchyPairingLimit_twoStep_form_gap
#print axioms strictJointCylinderCompletedTwoStepTransfer_form_gap_of_approximation
#print axioms anchorDecoratedDoubledTimeRate_completed_vacuum_form_gap_of_density

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedGapExtension
