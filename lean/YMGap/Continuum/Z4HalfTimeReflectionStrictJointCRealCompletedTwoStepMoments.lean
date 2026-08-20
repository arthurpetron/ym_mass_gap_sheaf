/-
# Powers and same-object moments of the completed two-step transfer

This file fixes the object whose decay is relevant to the mass-gap question.
The `n`-th power of the physical transfer `S = T^2` is definitionally the
already constructed completed time translation `T^(2n)`.  Its autocorrelation
is therefore formed with the same completed carrier and the same completed OS
inner form as the desired one-step gap.

Besides the semigroup, positivity, contraction, vacuum, and invariant-
complement laws, the file proves the exact moment identity

  <S^(m+n)x,x> = <S^m x,S^n x>

and its doubled specialization.  Completed Cauchy--Schwarz then gives the
dyadic moment inequality needed by any honest clustering-to-gap argument.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedEvenTimeInterval
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInnerLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTimeSelfAdjoint
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The concrete powers `S^n = T^(2n)` -/

/-- The `n`-th power of the completed physical two-step transfer. -/
def strictJointCylinderCompletedTwoStepPower
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (n : Nat) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle :=
  strictJointCylinderCompletedTimeTranslate hcoupling hle (n + n)

theorem strictJointCylinderCompletedTwoStepPower_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepPower hcoupling hle 0 vector = vector := by
  exact strictJointCylinderCompletedTimeTranslate_zero hcoupling hle vector

theorem strictJointCylinderCompletedTwoStepPower_one
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepPower hcoupling hle 1 vector =
      strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector :=
  rfl

theorem strictJointCylinderCompletedTwoStepPower_add
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepPower hcoupling hle
        (first + second) vector =
      strictJointCylinderCompletedTwoStepPower hcoupling hle first
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle second vector) := by
  unfold strictJointCylinderCompletedTwoStepPower
  have hshift :
      (first + second) + (first + second) =
        (first + first) + (second + second) := by omega
  rw [hshift]
  exact strictJointCylinderCompletedTimeTranslate_add
    hcoupling hle (first + first) (second + second) vector

theorem strictJointCylinderCompletedTwoStepPower_succ
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepPower hcoupling hle (n + 1) vector =
      strictJointCylinderCompletedTwoStepTransfer hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle n vector) := by
  simpa [Nat.one_add,
    strictJointCylinderCompletedTwoStepPower_one]
    using strictJointCylinderCompletedTwoStepPower_add
      hcoupling hle 1 n vector

theorem strictJointCylinderCompletedTwoStepPower_self_adjoint
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle n left) right =
      strictJointCylinderCompletedInner hcoupling hle left
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle n right) :=
  strictJointCylinderCompletedEvenTimeTranslate_self_adjoint
    hcoupling hle n left right

theorem strictJointCylinderCompletedTwoStepPower_positive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCnonneg
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle n vector) vector) :=
  strictJointCylinderCompletedEvenTimeTransferForm_nonneg
    hcoupling hle n vector

theorem strictJointCylinderCompletedTwoStepPower_form_le_identity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle n vector) vector)
      (strictJointCylinderCompletedInner hcoupling hle vector vector) :=
  strictJointCylinderCompletedEvenTimeTransferForm_le_identity
    hcoupling hle n vector

theorem strictJointCylinderCompletedTwoStepPower_normSq_le
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    CReal.RCle
      (strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector)
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector))
      (strictJointCylinderCompletedInner hcoupling hle vector vector) :=
  strictJointCylinderCompletedEvenTimeTranslate_normSq_le
    hcoupling hle n vector

theorem strictJointCylinderCompletedTwoStepPower_vacuum
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (n : Nat) :
    strictJointCylinderCompletedTwoStepPower hcoupling hle n
        (strictJointCylinderCompletionVacuum hcoupling hle) =
      strictJointCylinderCompletionVacuum hcoupling hle :=
  strictJointCylinderCompletedTimeTranslate_vacuum hcoupling hle (n + n)

theorem strictJointCylinderCompletedTwoStepPower_preserves_vacuumOrthogonal
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (n : Nat)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (horthogonal : StrictJointCylinderCompletionVacuumOrthogonal
      hcoupling hle vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hcoupling hle
      (strictJointCylinderCompletedTwoStepPower
        hcoupling hle n vector) :=
  strictJointCylinderCompletedEvenTimeTranslate_preserves_vacuumOrthogonal
    hcoupling hle n vector horthogonal

/-! ## 2. Same-object completed autocorrelations -/

/-- The autocorrelation sequence of one vector under the concrete completed
physical transfer. -/
def strictJointCylinderCompletedTwoStepAutocorrelation
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (n : Nat) : CReal.RC :=
  strictJointCylinderCompletedInner hcoupling hle
    (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector) vector

theorem strictJointCylinderCompletedTwoStepAutocorrelation_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector 0 =
      strictJointCylinderCompletedInner hcoupling hle vector vector := by
  unfold strictJointCylinderCompletedTwoStepAutocorrelation
  rw [strictJointCylinderCompletedTwoStepPower_zero]

theorem strictJointCylinderCompletedTwoStepAutocorrelation_one
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector 1 =
      strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepTransfer hcoupling hle vector)
        vector := by
  unfold strictJointCylinderCompletedTwoStepAutocorrelation
  rw [strictJointCylinderCompletedTwoStepPower_one]

theorem strictJointCylinderCompletedTwoStepAutocorrelation_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (n : Nat) :
    CReal.RCnonneg
      (strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector n) :=
  strictJointCylinderCompletedTwoStepPower_positive
    hcoupling hle n vector

theorem strictJointCylinderCompletedTwoStepAutocorrelation_le_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (n : Nat) :
    CReal.RCle
      (strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector n)
      (strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector 0) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_zero]
  exact strictJointCylinderCompletedTwoStepPower_form_le_identity
    hcoupling hle n vector

/-- The moment at `m+n` is the inner product of the two corresponding
propagated vectors.  This is the exact same-object semigroup identity. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_add
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (first second : Nat) :
    strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector (first + second) =
      strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle first vector)
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle second vector) := by
  unfold strictJointCylinderCompletedTwoStepAutocorrelation
  rw [strictJointCylinderCompletedTwoStepPower_add]
  calc
    strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle first
          (strictJointCylinderCompletedTwoStepPower
            hcoupling hle second vector)) vector =
      strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle second vector)
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle first vector) :=
        strictJointCylinderCompletedTwoStepPower_self_adjoint
          hcoupling hle first
            (strictJointCylinderCompletedTwoStepPower
              hcoupling hle second vector) vector
    _ = strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle first vector)
        (strictJointCylinderCompletedTwoStepPower
          hcoupling hle second vector) :=
      strictJointCylinderCompletedInner_symm hcoupling hle _ _

theorem strictJointCylinderCompletedTwoStepAutocorrelation_double
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (n : Nat) :
    strictJointCylinderCompletedTwoStepAutocorrelation
        hcoupling hle vector (n + n) =
      strictJointCylinderCompletedInner hcoupling hle
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector)
        (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector) :=
  strictJointCylinderCompletedTwoStepAutocorrelation_add
    hcoupling hle vector n n

/-- Dyadic log-convexity at the origin:
`m_n^2 <= m_(2n) m_0`.  This is the non-finite-dimensional analytic lever for
turning asymptotic decay of the same moments into a one-step spectral bound. -/
theorem strictJointCylinderCompletedTwoStepAutocorrelation_dyadic
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle)
    (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (strictJointCylinderCompletedTwoStepAutocorrelation
          hcoupling hle vector n)
        (strictJointCylinderCompletedTwoStepAutocorrelation
          hcoupling hle vector n))
      (CReal.RCmul
        (strictJointCylinderCompletedTwoStepAutocorrelation
          hcoupling hle vector (n + n))
        (strictJointCylinderCompletedTwoStepAutocorrelation
          hcoupling hle vector 0)) := by
  rw [strictJointCylinderCompletedTwoStepAutocorrelation_double,
    strictJointCylinderCompletedTwoStepAutocorrelation_zero]
  exact strictJointCylinderCompletedInner_cauchy_schwarz
    hcoupling hle
      (strictJointCylinderCompletedTwoStepPower hcoupling hle n vector)
      vector

#print axioms strictJointCylinderCompletedTwoStepPower
#print axioms strictJointCylinderCompletedTwoStepPower_add
#print axioms strictJointCylinderCompletedTwoStepPower_self_adjoint
#print axioms strictJointCylinderCompletedTwoStepPower_positive
#print axioms strictJointCylinderCompletedTwoStepPower_normSq_le
#print axioms strictJointCylinderCompletedTwoStepPower_vacuum
#print axioms strictJointCylinderCompletedTwoStepPower_preserves_vacuumOrthogonal
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_add
#print axioms strictJointCylinderCompletedTwoStepAutocorrelation_dyadic

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepMoments
