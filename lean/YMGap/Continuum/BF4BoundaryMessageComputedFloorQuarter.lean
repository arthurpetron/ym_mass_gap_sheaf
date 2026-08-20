/-
# Computed-floor data supplies physical quarter contraction

This is the final adapter for the constructive finite-floor reduction.  A
terminal certificate, nonzero nonnegative prefix rows, and the single
entrywise physical error estimate relative to the automatically computed
finite floor construct the literal BF4 boundary-message quarter certificate.
-/

import YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
import YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter

namespace YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter

open YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor
open YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter
open YMGap.Continuum.BF4BoundaryMessageProjectiveRefresh
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative

namespace MatchedPhysicalHalfAmplitudeComputedFloorErrorRows

/-- The computed-floor/error interface yields a uniform cross-ratio
certificate for the literal physical half-amplitude. -/
def toUniformPhysicalCrossRatioCertificate
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> YMGap.Constructive.Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
        Middle family law spacing coupling halfExtent diagonalOrder) :=
  YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toUniformPhysicalCrossRatioCertificate
    data.toTerminalFloorErrorRows

/-- Therefore the sole physical error field in the computed-floor interface
is sufficient for the terminal-independent quarter-contraction certificate. -/
def toUniformBoundaryMessageQuarterCertificate
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> YMGap.Constructive.Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
        Middle family law spacing coupling halfExtent diagonalOrder) :=
  YMGap.Continuum.BF4BoundaryMessagePhysicalTerminalFloorAdapter.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toUniformBoundaryMessageQuarterCertificate
    data.toTerminalFloorErrorRows

end MatchedPhysicalHalfAmplitudeComputedFloorErrorRows

end YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter

#print axioms YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter.MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.toUniformPhysicalCrossRatioCertificate
#print axioms YMGap.Continuum.BF4BoundaryMessageComputedFloorQuarter.MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.toUniformBoundaryMessageQuarterCertificate
