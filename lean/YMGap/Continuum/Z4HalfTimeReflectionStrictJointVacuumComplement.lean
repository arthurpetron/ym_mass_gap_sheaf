/-
# Vacuum stationarity for the completed strict-cylinder time semigroup

The strict-cylinder construction already supplies an infinite-volume
reflection form, an exact Euclidean-time action, its OS nonexpansiveness, and
a choice-free completion over all finite source boxes.  This file identifies
the constant cylinder as the vacuum, proves that canonical base transport and
time translation fix it, and descends that stationarity to the completed
carrier.

At the dense presentation level, the derived even-time one-sided covariance
then shows that the vacuum-orthogonal sector is invariant under every even
time translation.  No strict contraction is asserted: replacing the existing
nonexpansive bound by a factor strictly below one on this sector is the
remaining quantitative gap input.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointEvenTimeOSPositive
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointEvenTimeOSPositive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The constant cylinder and its exact geometric stationarity -/

/-- The constant-one strict cylinder presentation.  Its empty root list makes
the same vacuum observable available at every finite base. -/
def strictJointCylinderVacuum (base : Nat) :
    StrictJointCylinderVector base where
  roots := []
  rootsCanonical := by
    intro root hroot
    simp only [List.not_mem_nil] at hroot
  coefficient := fun _ => 1

/-- Euclidean-time translation fixes the constant cylinder exactly, including
the indexed change of source base. -/
theorem timeTranslateStrictJointCylinderVacuum
    (base shift : Nat) :
    timeTranslateStrictJointCylinderVector shift
        (strictJointCylinderVacuum base) =
      strictJointCylinderVacuum (base + shift) := by
  rfl

/-- Canonical enlargement of the source box fixes the constant cylinder
exactly. -/
theorem boxTransportStrictJointCylinderVacuum
    {base outer : Nat} (hbase : base ≤ outer) :
    boxTransportStrictJointCylinderVector hbase
        (strictJointCylinderVacuum base) =
      strictJointCylinderVacuum outer := by
  rfl

/-- The constant cylinder has exactly unit limiting reflection norm.  Thus the
stationary vector below is the normalized OS vacuum, not merely a fixed point
of the time action. -/
theorem strictJointCylinderVacuum_reflectionQuadratic_equiv_cone
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (base : Nat) :
    CReal.Equiv
      ((strictJointCylinderVacuum base).reflectionQuadratic hcoupling hle)
      CReal.cone := by
  apply CReal.Equiv_of_lifted_approx_equal
  intro stage
  apply CReal.ofQ'_equiv_of_eqv
  have hsupport :=
    centralNormalizedStrictJointFixedQuadraticSequence_eqv_supportGram
      coupling hcoupling base [] (fun _ => 1) stage
  have hfull := centralNormalizedSupportReflectionQuadratic_eq_full
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage) (fun _ => 1)
  have hone := centralNormalizedFullPhysicalReflectionQuadratic_one
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff base stage)
    (strictQueryBase base + stage)
  change
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base [] (fun _ => 1) stage ≈ 1
  exact Q'.eqv_trans _ _ _ hsupport
    (Q'.eqv_trans _ _ _ hfull hone)

/-! ## 2. The dense vacuum complement -/

/-- A strict-cylinder vector is in the vacuum complement when its reflected
matrix coefficient against the constant cylinder vanishes. -/
def StrictJointVacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) : Prop :=
  CReal.Equiv
    (strictJointCylinderReflectionBilinear hcoupling hle vector
      (strictJointCylinderVacuum base))
    CReal.czero

/-- Derived even-time self-adjointness and exact vacuum stationarity preserve
the vacuum complement.  This is an invariance theorem, not a strict spectral
estimate. -/
theorem evenTimeTranslate_preserves_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (horthogonal : StrictJointVacuumOrthogonal hcoupling hle vector) :
    StrictJointVacuumOrthogonal hcoupling hle
      (timeTranslateStrictJointCylinderVector (shift + shift) vector) := by
  let vacuum := strictJointCylinderVacuum base
  let targetVacuum := strictJointCylinderVacuum (base + (shift + shift))
  have hcovariance := strictJointEvenOneSidedTimeCovariance_derived
    hcoupling hle shift vacuum vector
  have hsymmetry := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (timeTranslateStrictJointCylinderVector (shift + shift) vector)
    targetVacuum
  have htransport :=
    boxTransportStrictJointCylinderVector_reflectionBilinear_equiv
      hcoupling hle (shift + shift) vector vacuum
  unfold StrictJointVacuumOrthogonal
  change CReal.Equiv
    (strictJointCylinderReflectionBilinear hcoupling hle
      (timeTranslateStrictJointCylinderVector (shift + shift) vector)
      targetVacuum)
    CReal.czero
  refine CReal.Equiv.trans hsymmetry ?_
  change StrictJointOneSidedTimeCovariance
    hcoupling hle (shift + shift) vacuum vector at hcovariance
  unfold StrictJointOneSidedTimeCovariance strictJointOneSidedTimeCross
    at hcovariance
  rw [boxTransportStrictJointCylinderVacuum,
    timeTranslateStrictJointCylinderVacuum] at hcovariance
  exact CReal.Equiv.trans hcovariance
    (CReal.Equiv.trans htransport horthogonal)

/-! ## 3. The exact non-strict transfer-form interval -/

/-- The even-time transfer form is bounded above by the source reflection
quadratic.  The doubled-time identity identifies the form with the norm of the
midpoint translate, and OS contraction supplies the bound. -/
theorem evenTimeStrictJointTransferForm_leEv_quadratic
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector (shift + shift) vector)
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base (shift + shift)) vector))
      (vector.reflectionQuadratic hcoupling hle) := by
  have hidentity := strictJointDoubledTimeMixedOSIdentity_derived
    hcoupling hle (Nat.le_refl (shift + shift)) vector
    (fixedStage := shift + shift)
  have hsymmetry := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (strictJointDoubledTimeMixedSource shift vector)
    (strictJointDoubledTimeMixedTarget shift vector)
  have hform : CReal.Equiv
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector shift vector))
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector (shift + shift) vector)
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base (shift + shift)) vector)) :=
    CReal.Equiv.trans hidentity hsymmetry
  have hcontract :=
    timeTranslatedStrictJointReflectionQuadratic_leEv_source
      hcoupling hle vector shift
  exact (CReal.leEv_congr hform (CReal.Equiv.refl _)).mp hcontract

/-- The literal even-time transfer form is positive and identity-bounded on
every dense strict-cylinder vector. -/
theorem evenTimeStrictJointTransferForm_interval
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv CReal.czero
        (strictJointCylinderReflectionBilinear hcoupling hle
          (timeTranslateStrictJointCylinderVector (shift + shift) vector)
          (boxTransportStrictJointCylinderVector
            (Nat.le_add_right base (shift + shift)) vector)) ∧
      CReal.leEv
        (strictJointCylinderReflectionBilinear hcoupling hle
          (timeTranslateStrictJointCylinderVector (shift + shift) vector)
          (boxTransportStrictJointCylinderVector
            (Nat.le_add_right base (shift + shift)) vector))
        (vector.reflectionQuadratic hcoupling hle) :=
  ⟨evenTimeStrictJointTransferForm_leEv_nonnegative
      hcoupling hle shift vector,
    evenTimeStrictJointTransferForm_leEv_quadratic
      hcoupling hle shift vector⟩

/-- The remaining quantitative spectral statement on the literal object.
It asks to replace the checked identity upper bound by one rational factor
strictly below one on the already invariant vacuum complement. -/
def StrictJointEvenTimeVacuumFormGap
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (shift : Nat) (separator : Q') : Prop :=
  (0 : Q') ≤ separator ∧ separator < (1 : Q') ∧
    ∀ {base : Nat} (vector : StrictJointCylinderVector base),
      StrictJointVacuumOrthogonal hcoupling hle vector →
      CReal.leEv
        (strictJointCylinderReflectionBilinear hcoupling hle
          (timeTranslateStrictJointCylinderVector (shift + shift) vector)
          (boxTransportStrictJointCylinderVector
            (Nat.le_add_right base (shift + shift)) vector))
        (CReal.mul (CReal.ofQ' separator)
          (vector.reflectionQuadratic hcoupling hle))

/-! ## 4. Vacuum stationarity on the completed carrier -/

/-- The base-zero constant cylinder as a staged dense vector. -/
def strictJointCylinderVacuumStage : StrictJointCylinderStage :=
  ⟨0, strictJointCylinderVacuum 0⟩

/-- Every translated vacuum stage represents the same algebraic direct-limit
vector. -/
theorem strictJointCylinderVacuumStage_timeTranslate_equivalent
    (shift : Nat) :
    StrictJointCylinderStageEquivalent
      (strictJointCylinderVacuumStage.timeTranslate shift)
      strictJointCylinderVacuumStage := by
  refine ⟨0 + shift, Nat.le_refl (0 + shift), Nat.zero_le (0 + shift), ?_⟩
  change
    boxTransportStrictJointCylinderVector (Nat.le_refl (0 + shift))
        (timeTranslateStrictJointCylinderVector shift
          (strictJointCylinderVacuum 0)) =
      boxTransportStrictJointCylinderVector (Nat.zero_le (0 + shift))
        (strictJointCylinderVacuum 0)
  rw [timeTranslateStrictJointCylinderVacuum,
    boxTransportStrictJointCylinderVacuum,
    boxTransportStrictJointCylinderVacuum]

/-- The canonical vacuum in the choice-free completed strict OS carrier. -/
def strictJointCylinderCompletionVacuum
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle :=
  (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
    strictJointCylinderVacuumStage

/-- A nonexpansive map sends a dense constant representative to the dense
constant representative of its image. -/
private theorem completionMap_embedRep_local
    {D : SquaredSeminorm} (T : D.Nonexpansive) (x : D.Carrier) :
    T.completionMap (D.embedRep x) = D.embedRep (T.toFun x) := by
  rfl

/-- The completed Euclidean-time semigroup fixes the canonical vacuum. -/
theorem strictJointCylinderCompletedTimeTranslate_vacuum
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (shift : Nat) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        (strictJointCylinderCompletionVacuum hcoupling hle) =
      strictJointCylinderCompletionVacuum hcoupling hle := by
  rw [show strictJointCylinderCompletedTimeTranslate hcoupling hle shift
      (strictJointCylinderCompletionVacuum hcoupling hle) =
        (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
          (strictJointCylinderVacuumStage.timeTranslate shift) by
      exact completionMap_embedRep_local
        (strictJointCylinderStageTimeTranslateNonexpansive
          hcoupling hle shift)
        strictJointCylinderVacuumStage]
  exact strictJointCylinderCompletion_embed_eq_of_stageEquivalent
    hcoupling hle
    (strictJointCylinderVacuumStage_timeTranslate_equivalent shift)

#print axioms timeTranslateStrictJointCylinderVacuum
#print axioms boxTransportStrictJointCylinderVacuum
#print axioms strictJointCylinderVacuum_reflectionQuadratic_equiv_cone
#print axioms evenTimeTranslate_preserves_vacuumOrthogonal
#print axioms evenTimeStrictJointTransferForm_leEv_quadratic
#print axioms evenTimeStrictJointTransferForm_interval
#print axioms strictJointCylinderVacuumStage_timeTranslate_equivalent
#print axioms strictJointCylinderCompletedTimeTranslate_vacuum

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
