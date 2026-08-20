/-
# The completed strict-cylinder OS inner form

The representative pairing limit is invariant under the explicit asymptotic
closeness relation defining the strict-cylinder completion.  This file uses
that theorem to descend the limit to an `RC = CReal/Equiv`-valued form on the
actual completed carrier and proves agreement with the staged pairing on the
dense constant image.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The representative pairing limit as an element of the genuine real
quotient. -/
def cauchyPairingLimitR
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    CReal.RC :=
  Quotient.mk CReal.crealSetoid (cauchyPairingLimit hcoupling hle X Y)

/-- The completed strict-cylinder OS inner form. -/
def strictJointCylinderCompletedInner
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle -> CReal.RC :=
  Quotient.lift₂
    (fun X Y => cauchyPairingLimitR hcoupling hle X Y)
    (fun X X' Y Y' hX hY => by
      rcases hX with ⟨hXdata⟩
      rcases hY with ⟨hYdata⟩
      exact Quotient.sound
        (cauchyPairingLimit_welldef
          hcoupling hle hXdata hYdata))

@[simp] theorem strictJointCylinderCompletedInner_mk
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (X Y : (strictJointCylinderStageSquaredSeminorm hcoupling hle).Cauchy) :
    strictJointCylinderCompletedInner hcoupling hle
        (Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid X)
        (Quotient.mk
          (strictJointCylinderStageSquaredSeminorm hcoupling hle).completionSetoid Y) =
      cauchyPairingLimitR hcoupling hle X Y := rfl

/-- On constant representatives the constructed outer limit is the original
staged pairing. -/
theorem cauchyPairingLimit_constant_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (cauchyPairingLimit hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).constant left)
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).constant right))
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) := by
  let X := (strictJointCylinderStageSquaredSeminorm hcoupling hle).constant left
  let Y := (strictJointCylinderStageSquaredSeminorm hcoupling hle).constant right
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ :=
    cauchyPairingSeq_converges hcoupling hle X Y epsilon hepsilon
  obtain ⟨K, hK⟩ := hN N (Nat.le_refl _)
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hforward, hbackward⟩ := hK k hk
  exact ⟨hbackward, hforward⟩

/-- The completed form extends the staged OS pairing on the dense image. -/
theorem strictJointCylinderCompletedInner_embedRep
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    strictJointCylinderCompletedInner hcoupling hle
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep left)
        ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep right) =
      Quotient.mk CReal.crealSetoid
        (strictJointCylinderStageReflectionBilinear
          hcoupling hle left right) := by
  exact Quotient.sound
    (cauchyPairingLimit_constant_equiv hcoupling hle left right)

#print axioms cauchyPairingLimitR
#print axioms strictJointCylinderCompletedInner
#print axioms cauchyPairingLimit_constant_equiv
#print axioms strictJointCylinderCompletedInner_embedRep

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
