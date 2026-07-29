/-
# AF row certificate for the positive reflected all-spin Mehler Gram

This module replaces the structurally unsuitable global alternating Taylor
endpoint by the finite positive feature Gram from
`BF4ReflectedAllSpinMehlerGramEndpoint`.

For this endpoint, raw symmetry, partition positivity, and normalized PSD are
theorems, not analytic fields.  The remaining spectral datum is exactly a
located physical-mean-zero Rayleigh rate.  The remaining comparison datum is
the existing numerator/partition/marginal AF row budget.

This is a strict reduction of the requested
`MatchedReflectedAllSpinAFRowCertificate` construction.  It does not fake the
two still-open estimates by selecting a large rate or tolerance.

## Axiom gate

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
import YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint

namespace YMGap.Continuum.BF4ReflectedAllSpinMehlerGramAFRow

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Spectral data with algebraic fields discharged -/

/-- Spectral datum for the displayed positive finite BF4 Mehler feature
Gram.  `diagonalOrder` counts the nonconstant shifted-complement terms; the
actual half-amplitude order is `diagonalOrder + 1`, so strict vacuum
positivity, symmetry, and PSD are all derived rather than assumed. -/
structure MehlerGramEndpointSpectralData
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent diagonalOrder crossOrder : Nat) : Type where
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
                  (bf4MehlerGramNumerator
                    (diagonalOrder + 1) crossOrder
                    left right)
                  (bf4MehlerGramVacuumPartition
                    (diagonalOrder + 1) crossOrder)
                  (bf4MehlerGramVacuumPartition_pos
                    (shiftedDiagonalVacuumCertificate
                      diagonalOrder)
                    crossOrder))) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

namespace MehlerGramEndpointSpectralData

/-- The positive feature Gram supplies the raw endpoint expected by the
existing AF row-relative normalization algebra. -/
def toRawEndpoint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (spectral :
      MehlerGramEndpointSpectralData
        w hw K halfExtent diagonalOrder crossOrder) :
    CentralPhysicalRawMehlerEndpoint
      w hw K halfExtent where
  numerator :=
    bf4MehlerGramNumerator
      (diagonalOrder + 1) crossOrder
  partition :=
    bf4MehlerGramVacuumPartition
      (diagonalOrder + 1) crossOrder
  partition_pos :=
    bf4MehlerGramVacuumPartition_pos
      (shiftedDiagonalVacuumCertificate
        diagonalOrder)
      crossOrder
  numerator_symmetric := by
    intro left right _ _
    exact bf4MehlerGramNumerator_symmetric
      (diagonalOrder + 1) crossOrder left right
  normalized_quadratic_nonnegative := by
    intro observable
    exact normalized_bf4MehlerGram_quadratic_nonnegative
      (shiftedDiagonalVacuumCertificate
        diagonalOrder)
      crossOrder
      (centralPositiveHalfStates
        w hw K halfExtent)
      observable
  rate := spectral.rate
  rate_nonnegative := spectral.rate_nonnegative
  normalized_meanZero_quadratic :=
    spectral.normalized_meanZero_quadratic

theorem toRawEndpoint_numerator
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent diagonalOrder crossOrder : Nat}
    (spectral :
      MehlerGramEndpointSpectralData
        w hw K halfExtent diagonalOrder crossOrder)
    (left right : EdgeLabelling) :
    spectral.toRawEndpoint.numerator left right =
      bf4MehlerGramNumerator
        (diagonalOrder + 1) crossOrder left right :=
  rfl

end MehlerGramEndpointSpectralData

/-! ## 2. Exact matched AF trajectory -/

/-- AF-uniform row certificate pinned to the positive BF4 Mehler feature
Gram.  Compared with the earlier global-Taylor structure, the certificate no
longer asks the analytic layer to assume symmetry or PSD. -/
structure MatchedReflectedAllSpinMehlerGramAFRowCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  diagonalOrder : Nat → Nat
  crossOrder : Nat → Nat
  spectral :
    ∀ scale,
      MehlerGramEndpointSpectralData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (crossOrder scale)
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  analyticBudget :
    ∀ scale,
      CentralPhysicalNumeratorPartitionBudget
        (spectral scale).toRawEndpoint epsilon

namespace MatchedReflectedAllSpinMehlerGramAFRowCertificate

def toUniformBudget
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinMehlerGramAFRowCertificate
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

/-- The scalar AF heat-time/spacing estimate remains pinned to the same
coupling schedule as the positive endpoint. -/
theorem heat_time_spacing_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinMehlerGramAFRowCertificate
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

/-- AF-uniform physical row comparison with the explicit positive all-spin
Mehler feature Gram. -/
theorem row_relative_estimate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent : Nat → Nat}
    (certificate :
      MatchedReflectedAllSpinMehlerGramAFRowCertificate
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

end MatchedReflectedAllSpinMehlerGramAFRowCertificate

#print axioms MehlerGramEndpointSpectralData.toRawEndpoint
#print axioms MehlerGramEndpointSpectralData.toRawEndpoint_numerator
#print axioms MatchedReflectedAllSpinMehlerGramAFRowCertificate.toUniformBudget
#print axioms MatchedReflectedAllSpinMehlerGramAFRowCertificate.heat_time_spacing_at
#print axioms MatchedReflectedAllSpinMehlerGramAFRowCertificate.row_relative_estimate

end YMGap.Continuum.BF4ReflectedAllSpinMehlerGramAFRow
