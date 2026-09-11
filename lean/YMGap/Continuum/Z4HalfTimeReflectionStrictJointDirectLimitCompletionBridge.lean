/-
# From the algebraic strict-cylinder direct limit to the OS completion

The staged CReal-seminorm completion already identifies every pair of stages
that are equal in the algebraic base direct limit.  This leaf packages that
fact as a canonical map from the algebraic quotient to the completed
carrier and proves that the map intertwines every indexed time translation.

This is carrier/action wiring only.  It does not construct a completed
bilinear form or claim completed self-adjointness.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitCompletionBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The canonical map from the algebraic staged direct limit to the completed
OS carrier.  Well-definedness is precisely the already proved fact that every
algebraic stage equivalence lies in the CReal-seminorm radical. -/
def StrictJointCylinderDirectLimit.toOSCompletion
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    StrictJointCylinderDirectLimit →
      StrictJointCylinderOSCompletion hcoupling hle :=
  Quotient.lift
    (fun stage =>
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep stage)
    (fun _ _ h =>
      strictJointCylinderCompletion_embed_eq_of_stageEquivalent
        hcoupling hle h)

@[simp] theorem strictJointCylinderDirectLimit_toOSCompletion_embed
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (stage : StrictJointCylinderStage) :
    StrictJointCylinderDirectLimit.toOSCompletion hcoupling hle
        (StrictJointCylinderDirectLimit.embed stage) =
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep stage :=
  rfl

/-- The completed time action maps a constant staged representative to the
constant representative of the translated stage. -/
@[simp] theorem strictJointCylinderCompletedTimeTranslate_embedRep
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : Nat) (stage : StrictJointCylinderStage) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        ((strictJointCylinderStageSquaredSeminorm
          hcoupling hle).embedRep stage) =
      (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (stage.timeTranslate shift) :=
  rfl

/-- The algebraic-to-completed map intertwines every time translation. -/
theorem StrictJointCylinderDirectLimit.toOSCompletion_timeTranslate
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : Nat) (vector : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.toOSCompletion hcoupling hle
        (StrictJointCylinderDirectLimit.timeTranslate shift vector) =
      strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        (StrictJointCylinderDirectLimit.toOSCompletion
          hcoupling hle vector) := by
  refine Quotient.inductionOn vector (fun stage => ?_)
  exact (strictJointCylinderCompletedTimeTranslate_embedRep
    hcoupling hle shift stage).symm

#print axioms StrictJointCylinderDirectLimit.toOSCompletion
#print axioms strictJointCylinderDirectLimit_toOSCompletion_embed
#print axioms strictJointCylinderCompletedTimeTranslate_embedRep
#print axioms StrictJointCylinderDirectLimit.toOSCompletion_timeTranslate

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitCompletionBridge
