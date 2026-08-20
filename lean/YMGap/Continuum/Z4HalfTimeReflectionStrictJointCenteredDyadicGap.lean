/-
# Dyadic gap removal directly for centered strict-cylinder moments

Exact dense-kernel approximation is not automatic over a rational-linear
carrier with a completed-real vacuum functional.  The robust alternative is
to keep the covariance centered before completion.  This file isolates the
three same-object moment laws needed by the existing constructive dyadic
argument and proves that, once they hold for a strict cylinder, its central
connected moment has the sharp common one-step rate `1/16` without any exact
dense vacuum-orthogonality hypothesis.

The geometric envelope is already proved for every strict cylinder.  The
remaining laws are positivity, contraction to time zero, and dyadic
log-convexity of the *centered* thermodynamic moment sequence.  They are
packaged in `Type` so their eventual finite-volume/Gram witnesses remain
visible.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredDyadicGap

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4CouplingParametricSignedThermodynamicClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The exact centered moment-law interface -/

/-- The three operator-moment laws required by constructive dyadic prefactor
removal, stated directly for the thermodynamic central connected moments of
one strict cylinder. -/
structure StrictJointDenseCentralMomentLaws
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) : Type where
  nonnegative : forall n : Nat,
    CReal.leEv CReal.czero
      (strictJointDenseCentralMoment hcoupling hle vector n)
  leZero : forall n : Nat,
    CReal.leEv
      (strictJointDenseCentralMoment hcoupling hle vector n)
      (strictJointDenseCentralMoment hcoupling hle vector 0)
  dyadic : forall n : Nat,
    CReal.leEv
      (CReal.mul
        (strictJointDenseCentralMoment hcoupling hle vector n)
        (strictJointDenseCentralMoment hcoupling hle vector n))
      (CReal.mul
        (strictJointDenseCentralMoment hcoupling hle vector (n + n))
        (strictJointDenseCentralMoment hcoupling hle vector 0))

/-- Uniform availability of the centered laws for every finite strict-cylinder
presentation.  This is the finite-volume/thermodynamic lemma now required by
the scalar-safe completion route. -/
def StrictJointAllDenseCentralMomentLaws
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) : Type :=
  forall (base : Nat) (vector : StrictJointCylinderVector base),
    StrictJointDenseCentralMomentLaws hcoupling hle vector

/-! ## 2. The unconditional geometric input -/

/-- Every central connected moment, without an orthogonality hypothesis,
obeys the already-constructed presentation-level geometric envelope. -/
theorem strictJointDenseCentralMoment_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.leEv
      (strictJointDenseCentralMoment hcoupling hle vector shift)
      (CReal.ofQ'
        (couplingParametricStrictSignedPositivePrefactor vector.roots.length
            (strictJointFingerprintSpace vector.roots.length)
            (strictJointFingerprintSpace vector.roots.length)
            vector.coefficient vector.coefficient *
          anchorDecoratedDoubledTimeRate ^ shift)) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage hstage => ?_⟩
  rw [strictJointDenseCentralMoment,
    orientedDoubledTimeCentralConnectedLimit_approx,
    CReal.ofQ'_approx]
  refine Q'.le_trans' _ _ _
    (Q'.le_abs_self
      (orientedDoubledTimeCentralConnectedSequence
        coupling hcoupling shift vector stage)) ?_
  refine Q'.le_trans' _ _ _
    (orientedDoubledTimeCentralConnectedSequence_abs_le_geometric
      hcoupling hle shift vector stage) ?_
  exact Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)

/-! ## 3. Dyadic contraction without exact dense centering -/

/-- The centered moment laws and the already-proved geometric envelope remove
the presentation prefactor and give the sharp common one-step rate.  No dense
vacuum-orthogonality assumption occurs in this theorem. -/
theorem strictJointDenseCentralMoment_le_rate_of_laws
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (laws : StrictJointDenseCentralMomentLaws hcoupling hle vector) :
    CReal.leEv
      (strictJointDenseCentralMoment hcoupling hle vector 1)
      (CReal.mul (CReal.ofQ' anchorDecoratedDoubledTimeRate)
        (strictJointDenseCentralMoment hcoupling hle vector 0)) := by
  apply dyadic_geometric_first_le
    (m := strictJointDenseCentralMoment hcoupling hle vector)
    (q := anchorDecoratedDoubledTimeRate)
    (P := couplingParametricStrictSignedPositivePrefactor vector.roots.length
      (strictJointFingerprintSpace vector.roots.length)
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient vector.coefficient)
  · exact anchorDecoratedDoubledTimeRate_pos
  · exact couplingParametricStrictSignedPositivePrefactor_pos
      vector.roots.length
      (strictJointFingerprintSpace vector.roots.length)
      (strictJointFingerprintSpace vector.roots.length)
      vector.coefficient vector.coefficient
  · exact laws.nonnegative
  · exact laws.leZero
  · exact laws.dyadic
  · exact strictJointDenseCentralMoment_le_geometric
      hcoupling hle vector

/-! ## 4. Compatibility with the proved dense vacuum complement -/

/-- The existing completed-moment laws provide the centered law package on
the already-proved exact dense vacuum complement.  This confirms that the new
interface genuinely extends the previous route rather than changing its
meaning. -/
def strictJointDenseCentralMomentLaws_of_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    StrictJointDenseCentralMomentLaws hcoupling hle vector where
  nonnegative := by
    intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_nonnegative
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
      hcoupling hle n vector horthogonal] at hn
    exact hn
  leZero := by
    intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_le_zero
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle n vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle 0 vector horthogonal] at hn
    exact hn
  dyadic := by
    intro n
    have hn := strictJointCylinderCompletedTwoStepAutocorrelation_dyadic
      hcoupling hle
      ((strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
        (StrictJointCylinderStage.mk base vector)) n
    rw [strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle n vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle (n + n) vector horthogonal,
      strictJointCylinderCompletedTwoStepAutocorrelation_embed_eq_centralConnectedLimit
        hcoupling hle 0 vector horthogonal] at hn
    exact hn

#print axioms StrictJointDenseCentralMomentLaws
#print axioms StrictJointAllDenseCentralMomentLaws
#print axioms strictJointDenseCentralMoment_le_geometric
#print axioms strictJointDenseCentralMoment_le_rate_of_laws
#print axioms strictJointDenseCentralMomentLaws_of_vacuumOrthogonal

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredDyadicGap
