/-
# The vacuum complement in the completed strict-cylinder OS carrier

The constant strict cylinder is already a normalized stationary vector at
finite base and in the squared-seminorm completion.  This file identifies its
completed OS norm with one, defines orthogonality to it using the constructed
`RC`-valued inner form, embeds the literal dense vacuum complement, and proves
invariance under the completed even-time semigroup.

No strict contraction on the complement is asserted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedEvenTimeInterval

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The completed vacuum is normalized -/

theorem strictJointCylinderVacuumStage_inner_self_equiv_one
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        strictJointCylinderVacuumStage strictJointCylinderVacuumStage)
      CReal.cone := by
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle strictJointCylinderVacuumStage
      strictJointCylinderVacuumStage (Nat.le_refl 0) (Nat.le_refl 0)
  have hstageClean : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (strictJointCylinderVacuum 0) (strictJointCylinderVacuum 0))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        strictJointCylinderVacuumStage strictJointCylinderVacuumStage) := by
    simpa only [strictJointCylinderVacuumStage,
      boxTransportStrictJointCylinderVector_refl] using hstage
  exact CReal.Equiv.trans (CReal.Equiv.symm hstageClean)
    (CReal.Equiv.trans
      (strictJointCylinderReflectionBilinear_self
        hcoupling hle (strictJointCylinderVacuum 0))
      (strictJointCylinderVacuum_reflectionQuadratic_equiv_cone
        hcoupling hle 0))

/-- The completed stationary vacuum has exactly unit OS norm. -/
theorem strictJointCylinderCompletionVacuum_inner_self_eq_one
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletionVacuum hcoupling hle)
        (strictJointCylinderCompletionVacuum hcoupling hle) =
      Quotient.mk CReal.crealSetoid CReal.cone := by
  unfold strictJointCylinderCompletionVacuum
  rw [strictJointCylinderCompletedInner_embedRep]
  exact Quotient.sound
    (strictJointCylinderVacuumStage_inner_self_equiv_one hcoupling hle)

/-! ## 2. The completed vacuum complement -/

/-- Orthogonality to the normalized vacuum in the actual completed carrier. -/
def StrictJointCylinderCompletionVacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) : Prop :=
  strictJointCylinderCompletedInner hcoupling hle vector
      (strictJointCylinderCompletionVacuum hcoupling hle) = CReal.RCzero

/-- A literal fixed-base vacuum-orthogonal cylinder embeds into the completed
vacuum complement. -/
theorem strictJointCylinderCompletionVacuumOrthogonal_embed
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) := by
  unfold StrictJointCylinderCompletionVacuumOrthogonal
    strictJointCylinderCompletionVacuum
  rw [strictJointCylinderCompletedInner_embedRep]
  apply Quotient.sound
  have hstage := strictJointCylinderStageReflectionBilinear_at_common
    hcoupling hle (StrictJointCylinderStage.mk base vector)
      strictJointCylinderVacuumStage (Nat.le_refl base) (Nat.zero_le base)
  have hstageClean : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        vector (strictJointCylinderVacuum base))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (StrictJointCylinderStage.mk base vector)
        strictJointCylinderVacuumStage) := by
    simpa only [strictJointCylinderVacuumStage,
      boxTransportStrictJointCylinderVector_refl,
      boxTransportStrictJointCylinderVacuum] using hstage
  exact CReal.Equiv.trans (CReal.Equiv.symm hstageClean) horthogonal

/-! ## 3. Even-time invariance -/

/-- Self-adjointness of the even subsemigroup and exact vacuum stationarity
make the completed vacuum complement invariant. -/
theorem strictJointCylinderCompletedEvenTimeTranslate_preserves_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle
      (strictJointCylinderCompletedTimeTranslate
        hcoupling hle (shift + shift) vector) := by
  unfold StrictJointCylinderCompletionVacuumOrthogonal at horthogonal ⊢
  calc
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle (shift + shift) vector)
        (strictJointCylinderCompletionVacuum hcoupling hle) =
      strictJointCylinderCompletedInner hcoupling hle vector
        (strictJointCylinderCompletedTimeTranslate hcoupling hle
          (shift + shift)
          (strictJointCylinderCompletionVacuum hcoupling hle)) :=
      strictJointCylinderCompletedEvenTimeTranslate_self_adjoint
        hcoupling hle shift vector
          (strictJointCylinderCompletionVacuum hcoupling hle)
    _ = strictJointCylinderCompletedInner hcoupling hle vector
        (strictJointCylinderCompletionVacuum hcoupling hle) := by
      rw [strictJointCylinderCompletedTimeTranslate_vacuum]
    _ = CReal.RCzero := horthogonal

#print axioms strictJointCylinderVacuumStage_inner_self_equiv_one
#print axioms strictJointCylinderCompletionVacuum_inner_self_eq_one
#print axioms strictJointCylinderCompletionVacuumOrthogonal_embed
#print axioms strictJointCylinderCompletedEvenTimeTranslate_preserves_vacuumOrthogonal

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
