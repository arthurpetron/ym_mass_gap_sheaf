/-
# AF row-relative comparison pinned to the reflected all-spin BF4 endpoint

`BF4AFUniformRowRelativeBudget` proves the normalization algebra for an
arbitrary signed reference endpoint.  This file removes that remaining
arbitrariness.  Its reference numerator is definitionally the rational
Taylor approximation of the geometric all-spin BF4 double-Haar coefficient,
whose equality with constructive polarization of the compact physical
quadratic was proved in `BF4ReflectedAllSpinPeterWeylBridge`.

The scale family is also pinned to the exact matched BF4 trajectory:

* weight `blockedWeight family (coupling scale)`;
* moving cutoff `matchedPhysicalSpacingBits family coupling scale`;
* the same `CubicMarginLaw` and `PhysicalSpacingEnvelope` used to construct
  `physicalAFEnvelope`.

The remaining analytic input is split honestly:

1. a spectral certificate for the displayed rational all-spin Taylor
   endpoint;
2. the already-sharpened numerator/partition/marginal budget comparing the
   physical reflected Choi kernel with that endpoint.

Given those data, the AF-uniform row-relative estimate is unconditional
finite rational algebra.  No unrelated endpoint matrix can inhabit the
interface.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
import YMGap.Continuum.BF4AFUniformRowRelativeBudget
import YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory

namespace YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative

set_option maxRecDepth 100000
set_option maxHeartbeats 100000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinPeterWeylBridge
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact matched AF carrier -/

/-- The exact rational blocked BF4 weight at one scale. -/
def matchedAllSpinWeight
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Q' :=
  blockedWeight family (coupling scale)

theorem matchedAllSpinWeight_pos
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) :
    (0 : Q') <
      matchedAllSpinWeight family coupling scale :=
  blockedWeight_pos family (coupling scale)

theorem matchedAllSpinWeight_nonnegative
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) :
    (0 : Q') ≤
      matchedAllSpinWeight family coupling scale :=
  Q'.le_of_lt
    (matchedAllSpinWeight_pos family coupling scale)

/-- The exact same-action Peter--Weyl cutoff of the matched block output. -/
def matchedAllSpinCutoff
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Nat :=
  matchedPhysicalSpacingBits family coupling scale

/-! ## 2. Spectral data for the displayed all-spin rational endpoint -/

/-- Vacuum--vacuum coefficient used to normalize the rational geometric
endpoint.  The partition is not an independent field of the certificate. -/
def geometricTaylorVacuumPartition (order : Nat) : Q' :=
  geometricMehlerTaylorPartial
    (fun _ => 0) (fun _ => 0) order

/-- Spectral certificate for one explicit rational Taylor approximation of
the reflected all-spin endpoint.

Unlike `CentralPhysicalRawMehlerEndpoint`, neither the numerator nor the
partition is a field: they are definitionally the geometric all-spin Taylor
coefficient and its vacuum--vacuum value.
-/
structure GeometricTaylorEndpointSpectralData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent order : Nat) : Type where
  partition_pos :
    (0 : Q') < geometricTaylorVacuumPartition order
  numerator_symmetric :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      right ∈ centralPositiveHalfStates w hw K halfExtent →
        geometricMehlerTaylorPartial left right order ≈
          geometricMehlerTaylorPartial right left order
  normalized_quadratic_nonnegative :
    ∀ observable : EdgeLabelling → Q',
      (0 : Q') ≤
        finiteJointQuadratic
          (centralPositiveHalfStates w hw K halfExtent)
          observable
          (fun left right =>
            Q'.divPos
              (geometricMehlerTaylorPartial
                left right order)
              (geometricTaylorVacuumPartition order)
              partition_pos)
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  normalized_meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero
        w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates
                w hw K halfExtent)
              observable
              (fun left right =>
                Q'.divPos
                (geometricMehlerTaylorPartial
                    left right order)
                  (geometricTaylorVacuumPartition order)
                  partition_pos)) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

namespace GeometricTaylorEndpointSpectralData

/-- Forget only the geometric presentation, producing the raw endpoint
consumed by the existing row-relative algebra. -/
def toRawEndpoint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent order : Nat}
    (spectral :
      GeometricTaylorEndpointSpectralData
        w hw K halfExtent order) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator := fun left right =>
    geometricMehlerTaylorPartial left right order
  partition := geometricTaylorVacuumPartition order
  partition_pos := spectral.partition_pos
  numerator_symmetric :=
    spectral.numerator_symmetric
  normalized_quadratic_nonnegative :=
    spectral.normalized_quadratic_nonnegative
  rate := spectral.rate
  rate_nonnegative := spectral.rate_nonnegative
  normalized_meanZero_quadratic :=
    spectral.normalized_meanZero_quadratic

/-- The raw numerator is literally the polarized compact physical Taylor
partial.  This is the reflected Peter--Weyl carrier bridge at the rational
endpoint used by the AF budget. -/
theorem numerator_eq_reflectedPhysical
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent order : Nat}
    (spectral :
      GeometricTaylorEndpointSpectralData
        w hw K halfExtent order)
    (left right : EdgeLabelling) :
    (spectral.toRawEndpoint.numerator left right) ≈
      reflectedPhysicalTaylorPartial
        left right order := by
  exact Q'.eqv_symm
    (reflectedPhysicalTaylorPartial_eq_geometric
      left right order)

end GeometricTaylorEndpointSpectralData

/-! ## 3. AF-uniform analytic certificate on the physical trajectory -/

/-- The remaining Yang--Mills analytic certificate, now pinned simultaneously
to the exact matched AF trajectory and the reflected all-spin endpoint.

The `analyticBudget` field is strictly more specific than the generic budget:
its endpoint is definitionally constructed from `geometricMehlerTaylorPartial`
at the displayed scale-dependent order.
-/
structure MatchedReflectedAllSpinAFRowCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  order : Nat → Nat
  spectral :
    ∀ scale,
      GeometricTaylorEndpointSpectralData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (order scale)
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  analyticBudget :
    ∀ scale,
      CentralPhysicalNumeratorPartitionBudget
        (spectral scale).toRawEndpoint epsilon

namespace MatchedReflectedAllSpinAFRowCertificate

/-- The certificate forgets to the generic AF-uniform row budget without
changing its weight, cutoff, endpoint numerator, or tolerance. -/
def toUniformBudget
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinAFRowCertificate
        family law spacing coupling halfExtent) :
    CentralPhysicalAFUniformNumeratorPartitionBudget
      (matchedAllSpinWeight family coupling)
      (matchedAllSpinWeight_nonnegative family coupling)
      (matchedAllSpinCutoff family coupling)
      halfExtent where
  epsilon := certificate.epsilon
  epsilon_nonnegative :=
    certificate.epsilon_nonnegative
  endpoint := fun scale =>
    (certificate.spectral scale).toRawEndpoint
  analyticBudget :=
    certificate.analyticBudget

/-- Every raw reference numerator in the uniform budget is the exact
finite reflected polarization of the geometric all-spin wavefunctions. -/
theorem endpoint_numerator_eq_reflectedPhysical
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinAFRowCertificate
        family law spacing coupling halfExtent)
    (scale : Nat) (left right : EdgeLabelling) :
    ((certificate.toUniformBudget.endpoint scale).numerator
        left right) ≈
      reflectedPhysicalTaylorPartial
        left right (certificate.order scale) :=
  (certificate.spectral scale).numerator_eq_reflectedPhysical
    left right

/-- The scalar AF heat-time/spacing estimate holds on exactly the same
coupling schedule used by the all-spin endpoint cutoff. -/
theorem heat_time_spacing_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinAFRowCertificate
        family law spacing coupling halfExtent)
    (scale : Nat) :
    BF4AFHeatSpacing.heatSpacingRate
          (physicalAFEnvelope family law spacing) *
        spacing.a (coupling scale) ≤
      BF4AFHeatSpacing.quarter *
        BF4MatchedPhysicalAFBridge.physicalTime
          (coupling scale) := by
  exact BF4AFHeatSpacing.heat_time_ge_rate_mul_spacing
    (physicalAFEnvelope family law spacing)
    (coupling scale)
    (certificate.coupling_pos scale)
    (certificate.coupling_le_window scale)

/-- **AF-uniform row-relative estimate for the reflected all-spin endpoint.**

The physical matrix is the exact normalized reflected Choi kernel.  The
reference matrix is the rational geometric BF4 all-spin double-Haar endpoint
at `certificate.order scale`.  The same rational `epsilon` pays every row at
every scale.
-/
theorem row_relative_estimate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinAFRowCertificate
        family law spacing coupling halfExtent)
    (scale : Nat)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)) :
    finiteJointDifferenceAbsRowMass
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralNormalizedPhysicalReflectedKernel
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (certificate.toUniformBudget.endpoint scale).joint
        source ≤
      certificate.epsilon *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source := by
  exact certificate.toUniformBudget.row_relative_error_at
    scale hsource

end MatchedReflectedAllSpinAFRowCertificate

end YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative

#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.matchedAllSpinWeight_nonnegative
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.GeometricTaylorEndpointSpectralData.toRawEndpoint
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.GeometricTaylorEndpointSpectralData.numerator_eq_reflectedPhysical
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.MatchedReflectedAllSpinAFRowCertificate.toUniformBudget
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.MatchedReflectedAllSpinAFRowCertificate.endpoint_numerator_eq_reflectedPhysical
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.MatchedReflectedAllSpinAFRowCertificate.heat_time_spacing_at
#print axioms YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.MatchedReflectedAllSpinAFRowCertificate.row_relative_estimate
