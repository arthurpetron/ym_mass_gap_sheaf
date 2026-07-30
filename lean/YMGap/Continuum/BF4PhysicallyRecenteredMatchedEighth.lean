/-
# Matched BF4 quarter theorem with the physically recentered endpoint

The stationary-vacuum calibrated endpoint has the correct normalized joint,
but its historical rate was inherited by scaling a pre-calibration row
majorant.  `BF4PhysicalRecenteredEndpointRate` replaces only that rate by the
exact Schur maximum of the calibrated joint minus `pi tensor pi`.

This module installs the corrected endpoint on the matched AF carrier.  Its
two analytic inputs are now literally:

1. the all-row estimate for the physically centered calibrated endpoint;
2. the physical-minus-endpoint all-row estimate.

It also transports the conditionally integrated fixed-magnetic realization
through the rate-only recentering.  Thus the second estimate continues to
follow from the collapsed active boundary-weight window, while the first is
free of the obsolete inherited vacuum term.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse
import YMGap.Continuum.BF4PhysicalRecenteredEndpointRate

namespace YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SymmetricReferenceOperatorComparison
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Corrected endpoint on the matched carrier -/

/-- The physically recentered calibrated endpoint at one matched scale. -/
def matchedPhysicallyRecenteredMehlerGramRawEndpointAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalRawMehlerEndpoint
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  physicallyRecenteredVacuumCalibratedMehlerGramRawEndpoint
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative
      family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (halfExtent scale)
    (diagonalOrder scale)
    (crossOrder scale)

/-- Exact sharp physical-minus-reference row maximum at one matched scale. -/
def matchedPhysicallyRecenteredSharpComparisonAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) : Q' :=
  physicalNormalizedJointMaxRowRatio
    (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)

/-- Signed symmetric-reference comparison built from the corrected endpoint
and its exact row maximum. -/
def matchedPhysicallyRecenteredReferenceComparisonAt
    (family : MatchedBlockFamily)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat)
    (scale : Nat) :
    CentralPhysicalSymmetricReferenceComparison
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale) :=
  exactPhysicalNormalizedJointReferenceComparison
    (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)

/-! ## 2. The two literal all-row eighth estimates -/

/-- Corrected spacing-uniform analytic certificate.

Both eighths are stated before a finite maximum is taken.  The spectral row
uses the exact post-calibration centering; the comparison row is the literal
physical-minus-calibrated-endpoint error. -/
structure MatchedPhysicallyRecenteredRowwiseEighthEstimates
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_centered_row_eighth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        physicalCenteredEndpointRowMass
            (matchedVacuumCalibratedMehlerGramRawEndpointAt
              family coupling halfExtent
              diagonalOrder crossOrder scale)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) source
  comparison_row_eighth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        physicalNormalizedJointRowError
            (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
              family coupling halfExtent
              diagonalOrder crossOrder scale)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) source

namespace MatchedPhysicallyRecenteredRowwiseEighthEstimates

/-- The first row family proves the corrected spectral eighth at every
matched scale. -/
theorem spectral_eighth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (estimates :
      MatchedPhysicallyRecenteredRowwiseEighthEstimates
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat) :
    (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
        family coupling halfExtent
        diagonalOrder crossOrder scale).rate ≤
      Q'.mkPos 1 8 (by decide) := by
  exact
    (physicallyRecenteredVacuumCalibrated_rate_le_eighth_iff_rows
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative
        family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (diagonalOrder scale)
      (crossOrder scale)).2
      (estimates.spectral_centered_row_eighth scale)

/-- The second row family proves the exact comparison maximum eighth. -/
theorem comparison_eighth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (estimates :
      MatchedPhysicallyRecenteredRowwiseEighthEstimates
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat) :
    matchedPhysicallyRecenteredSharpComparisonAt
        family coupling halfExtent
        diagonalOrder crossOrder scale ≤
      Q'.mkPos 1 8 (by decide) := by
  exact physicalNormalizedJointMaxRowRatio_le_of_row_relative
    (matchedPhysicallyRecenteredMehlerGramRawEndpointAt
      family coupling halfExtent
      diagonalOrder crossOrder scale)
    (Q'.mkPos 1 8 (by decide))
    (by decide)
    (estimates.comparison_row_eighth scale)

/-- **Corrected matched quarter theorem.**

The two literal row eighths add to a physical mean-zero contraction by
`1/4` at every scale. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (estimates :
      MatchedPhysicallyRecenteredRowwiseEighthEstimates
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable := by
  let comparison :=
    matchedPhysicallyRecenteredReferenceComparisonAt
      family coupling halfExtent
      diagonalOrder crossOrder scale
  have hquarter :
      comparison.reference.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide) := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add
        (estimates.spectral_eighth scale)
        (estimates.comparison_eighth scale)) ?_
    decide
  exact
    CentralPhysicalSymmetricReferenceComparison.physical_markov_quadratic_abs_le_quarter
      comparison hquarter observable hmean

end MatchedPhysicallyRecenteredRowwiseEighthEstimates

/-! ## 3. Transport of the collapsed fixed-magnetic proof -/

/-- A collapsed fixed-magnetic realization survives physical recentering
because the rate-only adapter leaves its normalized joint unchanged. -/
def recenterCollapsedActiveFixedMagneticEndpointRealization
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half}
    (realization :
      CollapsedActiveFixedMagneticEndpointRealization
        hw K half endpoint) :
    CollapsedActiveFixedMagneticEndpointRealization
      hw K half
      (physicalRecenterRawMehlerEndpointRate endpoint) where
  referenceWeight := realization.referenceWeight
  joint_identification := by
    intro left hleft right hright
    exact Q'.eqv_trans _ _ _
      (physicalRecenterRawMehlerEndpointRate_joint
        endpoint left right)
      (realization.joint_identification
        left hleft right hright)
  collapsed_active_eighth :=
    realization.collapsed_active_eighth

/-- Matched collapsed realizations plus the corrected centered row estimate
inhabit both row fields of the final corrected quarter theorem. -/
structure MatchedCollapsedActiveRecenteredEighthRealization
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  spectral_centered_row_eighth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        physicalCenteredEndpointRowMass
            (matchedVacuumCalibratedMehlerGramRawEndpointAt
              family coupling halfExtent
              diagonalOrder crossOrder scale)
            source ≤
          Q'.mkPos 1 8 (by decide) *
            centralPhysicalRowMarginal
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative
                family coupling scale)
              (matchedAllSpinCutoff family coupling scale)
              (halfExtent scale) source
  collapsed :
    ∀ scale,
      CollapsedActiveFixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)

namespace MatchedCollapsedActiveRecenteredEighthRealization

/-- Conditional integration proves the complete second row field; the
supplied corrected centered rows provide the first. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (realization :
      MatchedCollapsedActiveRecenteredEighthRealization
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := realization.coupling_pos
  coupling_le_window := realization.coupling_le_window
  spectral_centered_row_eighth :=
    realization.spectral_centered_row_eighth
  comparison_row_eighth := by
    intro scale source hsource
    let recentered :=
      recenterCollapsedActiveFixedMagneticEndpointRealization
        (realization.collapsed scale)
    exact recentered.physicalNormalizedJointRowError_le_eighth
      hsource

end MatchedCollapsedActiveRecenteredEighthRealization

end YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth.MatchedPhysicallyRecenteredRowwiseEighthEstimates.spectral_eighth
#print axioms YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth.MatchedPhysicallyRecenteredRowwiseEighthEstimates.comparison_eighth
#print axioms YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth.MatchedPhysicallyRecenteredRowwiseEighthEstimates.physical_quarter_uniform
#print axioms YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth.recenterCollapsedActiveFixedMagneticEndpointRealization
#print axioms YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth.MatchedCollapsedActiveRecenteredEighthRealization.toRowwiseEighthEstimates
