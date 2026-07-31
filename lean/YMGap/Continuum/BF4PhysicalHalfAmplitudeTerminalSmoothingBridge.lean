/-
# Terminal smoothing to the physical BF4 posterior eighths

For the genuine half-amplitude, the analytically natural regrouping is

  A(source,boundary)
    = sum_middle prefix(source,middle) * terminal(middle,boundary).

All nonnegative interior Feynman--Kac weights may be absorbed into
`prefix`.  A positive terminal kernel then controls the complete
cross-ratio diameter of `A`, independently of the oscillation and size of
that prefix.

This file connects the existing terminal-smoothing theorem to the exact
physical half-amplitude projective consumer.  Consequently one
spacing-uniform terminal certificate with squared spread at most `65/64`
inhabits both physical rowwise eighth estimates.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge
import YMGap.Continuum.BF4TerminalSmoothingProjective

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRetainedHarnackBridge
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## Spacing-uniform terminal factorization -/

/-- A scale-varying exact terminal-smoothing factorization of the genuine
BF4 half-amplitude.  The middle carrier may grow with the cutoff. -/
structure MatchedPhysicalHalfAmplitudeTerminalSmoothingRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  middles :
    ∀ scale, List (Middle scale)
  prefixWeight :
    ∀ scale, EdgeLabelling → Middle scale → Q'
  terminal :
    ∀ scale, Middle scale → EdgeLabelling → Q'
  prefixRows :
    ∀ scale,
      PositivePrefixRows
        (prefixWeight scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (middles scale)
  terminalCertificate :
    ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (middles scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  spread_square_le :
    ∀ scale,
      (terminalCertificate scale).spread *
          (terminalCertificate scale).spread ≤
        anchoredProjectiveCeiling
  physical_identification :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            centralHalfAmplitude
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) source boundary ≈
              terminalSmoothedKernel
                (prefixWeight scale)
                (terminal scale)
                (middles scale)
                source boundary

namespace MatchedPhysicalHalfAmplitudeTerminalSmoothingRows

/-- Exact terminal regrouping and the terminal cross-ratio certificate
supply the single physical half-amplitude projective field. -/
def toHalfAmplitudeProjectiveRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalSmoothingRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedHalfAmplitudeProjectiveRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  spread := fun scale =>
    (data.terminalCertificate scale).spread
  spread_square_le := data.spread_square_le
  half_amplitude_cross_ratio := by
    intro scale
    exact
      crossRatio_of_entrywise_grouped_identification
        (centralHalfAmplitude
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (terminalSmoothedKernel
          (data.prefixWeight scale)
          (data.terminal scale)
          (data.middles scale))
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (data.terminalCertificate scale).spread
        (terminalSmoothedCertificate
          (data.terminalCertificate scale)
          (data.prefixRows scale)).crossRatioBound
        (data.physical_identification scale)

/-- Therefore one exact physical terminal factorization with the
spacing-uniform `65/64` terminal spread inhabits both requested rowwise
eighth estimates. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalSmoothingRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toHalfAmplitudeProjectiveRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalHalfAmplitudeTerminalSmoothingRows

end YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge.MatchedPhysicalHalfAmplitudeTerminalSmoothingRows.toHalfAmplitudeProjectiveRows
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge.MatchedPhysicalHalfAmplitudeTerminalSmoothingRows.toRowwiseEighthEstimates
