/-
# Computed terminal-smoothed floors for the physical BF4 boundary message

Strict positivity on the retained source and boundary lists already implies
an exact positive rational floor: both lists are explicitly finite and both
contain the vacuum labelling.  This file computes that floor by finite list
recursion and removes it from the analytic hypotheses of the physical
terminal-perturbation route.

The remaining physical input is precisely the entrywise estimate

  |physical - ideal| <= computedFloor / 2048.

Thus no compactness, choice, or continuum minimum is hidden in the floor.
-/

import YMGap.Continuum.BF4BoundaryMessageFinitePositiveFloor
import YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

namespace YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4BoundaryMessageFinitePositiveFloor
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. The automatically computed floor -/

/-- The terminal-smoothed ideal kernel has a computable positive minimum on
the finite physical source-by-boundary rectangle. -/
def terminalSmoothedFiniteFloor
    {Middle : Type}
    {w : Q'} (hw : (0 : Q') <= w)
    (K halfExtent : Nat)
    (middles : List Middle)
    (prefixWeight : EdgeLabelling -> Middle -> Q')
    (terminal : Middle -> EdgeLabelling -> Q')
    (prefixRows :
      PositivePrefixRows
        prefixWeight
        (centralPositiveHalfStates
          w hw K halfExtent)
        middles)
    (terminalCertificate :
      FiniteCrossRatioDiameterCertificate
        terminal middles
        (centralBoundaryChannels K halfExtent)) :
    FinitePositiveKernelFloor
      (centralPositiveHalfStates
        w hw K halfExtent)
      (centralBoundaryChannels K halfExtent)
      (terminalSmoothedKernel prefixWeight terminal middles) := by
  let sources :=
    centralPositiveHalfStates
      w hw K halfExtent
  let targets :=
    centralBoundaryChannels K halfExtent
  let idealCertificate :=
    terminalSmoothedCertificate terminalCertificate prefixRows
  exact finitePositiveKernelFloorOfNonempty
    sources targets
    (terminalSmoothedKernel prefixWeight terminal middles)
    zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralPositiveHalfStates
      hw K halfExtent)
    zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralBoundaryChannels
      K halfExtent)
    idealCertificate.strictlyPositive

/-! ## 2. Scale-indexed interface with only the error estimate left -/

/-- All algebraic terminal-smoothing data, with the positive ideal floor
computed internally.  The final field is the sole remaining physical
entrywise comparison needed by the direct boundary-message route. -/
structure MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
    (Middle : Nat -> Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat -> Q')
    (halfExtent diagonalOrder : Nat -> Nat) : Type where
  coupling_pos :
    forall scale, (0 : Q') < coupling scale
  coupling_le_window :
    forall scale, coupling scale <= law.g₁
  calibrated_harnack :
    forall scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) (diagonalOrder scale) 0
  middles : forall scale, List (Middle scale)
  prefixWeight : forall scale, EdgeLabelling -> Middle scale -> Q'
  terminal : forall scale, Middle scale -> EdgeLabelling -> Q'
  prefixRows :
    forall scale,
      PositivePrefixRows
        (prefixWeight scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (middles scale)
  terminalCertificate :
    forall scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale) (middles scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  terminal_spread_square_le_split :
    forall scale,
      (terminalCertificate scale).spread *
          (terminalCertificate scale).spread <=
        splitProjectiveCeiling
  physical_error :
    forall scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) ->
        forall boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) ->
            Q'.abs
                (centralHalfAmplitude
                    (matchedAllSpinWeight family coupling scale)
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale) source boundary +
                  -terminalSmoothedKernel
                    (prefixWeight scale)
                    (terminal scale)
                    (middles scale)
                    source boundary) <=
              physicalRelativeErrorTolerance *
                (terminalSmoothedFiniteFloor
                  (matchedAllSpinWeight_nonnegative
                    family coupling scale)
                  (matchedAllSpinCutoff family coupling scale)
                  (halfExtent scale)
                  (middles scale)
                  (prefixWeight scale)
                  (terminal scale)
                  (prefixRows scale)
                  (terminalCertificate scale)).floor

namespace MatchedPhysicalHalfAmplitudeComputedFloorErrorRows

/-- The computed-floor interface constructs the former explicit-floor
package, so every downstream physical quarter-contraction theorem applies
unchanged. -/
def toTerminalFloorErrorRows
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
        Middle family law spacing coupling halfExtent diagonalOrder) :
    MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
      Middle family law spacing coupling halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  middles := data.middles
  prefixWeight := data.prefixWeight
  terminal := data.terminal
  prefixRows := data.prefixRows
  terminalCertificate := data.terminalCertificate
  terminal_spread_square_le_split :=
    data.terminal_spread_square_le_split
  idealFloor := fun scale =>
    (terminalSmoothedFiniteFloor
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (data.middles scale)
      (data.prefixWeight scale)
      (data.terminal scale)
      (data.prefixRows scale)
      (data.terminalCertificate scale)).floor
  ideal_floor := by
    intro scale source source_mem boundary boundary_mem
    exact
      (terminalSmoothedFiniteFloor
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (data.middles scale)
        (data.prefixWeight scale)
        (data.terminal scale)
        (data.prefixRows scale)
        (data.terminalCertificate scale)).floor_le
          source source_mem boundary boundary_mem
  physical_error := data.physical_error

/-- The automatically selected ideal floor is strictly positive at every
scale. -/
theorem computedIdealFloor_pos
    {Middle : Nat -> Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {halfExtent diagonalOrder : Nat -> Nat}
    (data :
      MatchedPhysicalHalfAmplitudeComputedFloorErrorRows
        Middle family law spacing coupling halfExtent diagonalOrder)
    (scale : Nat) :
    (0 : Q') < data.toTerminalFloorErrorRows.idealFloor scale := by
  exact
    (terminalSmoothedFiniteFloor
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (halfExtent scale)
      (data.middles scale)
      (data.prefixWeight scale)
      (data.terminal scale)
      (data.prefixRows scale)
      (data.terminalCertificate scale)).floor_pos

end MatchedPhysicalHalfAmplitudeComputedFloorErrorRows

end YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor

#print axioms YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor.terminalSmoothedFiniteFloor
#print axioms YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor.MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.toTerminalFloorErrorRows
#print axioms YMGap.Continuum.BF4BoundaryMessageComputedTerminalFloor.MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.computedIdealFloor_pos
